include Llvm
open Meta

(* the following exception shouldn't get thrown at all, unless, of course, there are bugs. *)
exception TcInconsistency     of unit meta * string
exception BrokenFunction      of string meta
exception BrokenModule        of string * string
exception CgLocalVarNotFound  of string meta * int
exception CgGlobalVarNotFound of string meta

module Lv = Core.Map.Make (Core.Int)
type lvenv = (string * llvalue) Lv.t

module Pool = Core.Hashtbl.Make (Core.String)
type pool = llvalue Pool.t

type cgenv = {
    context : llcontext;
    cgmod   : llmodule;
    builder : llbuilder;
    (* the constant pool for all strings *)
    str_pool : pool;
    (* count the index of inits *)
    init_acc : int ref;
  }

let new_cgenv name : cgenv =
  let ctx = global_context () in
  let m   = create_module ctx name in
  let bld = builder ctx in
  {
    context  = ctx;
    cgmod    = m;
    builder  = bld;
    str_pool = Pool.create ();
    init_acc = ref 0;
  }

module type CgEnv = sig
  val g : cgenv
end

module Basics (X : CgEnv) = struct
  open X

  let bool_type  = i1_type g.context
  let rune_type  = i32_type g.context
  let int_type   = i32_type g.context
  let float_type = double_type g.context
  let void_type  = void_type g.context
  let i8         = i8_type g.context
  let str_type   = pointer_type i8
  let voidp_type = pointer_type i8
  let bytep_type = pointer_type i8
  let size_type  = if Sys.word_size = 32 then i32_type g.context else i64_type g.context

  let ty_prefix = "ty."
  let ty_name n =
    (* we mangle the name for a type definition *)
    let mangled = Format.sprintf "%s-%d-%d-%d-%d" n.data n.start_l n.start_c n.end_l n.end_c in
    ty_prefix ^ mangled

  let named_struct n =
    type_by_name g.cgmod (ty_name n)

  let true_val  = const_int bool_type 1
  let false_val = const_int bool_type 0
  let m1_val t  = const_int t (-1)
  let zeroi_val = const_int int_type 0
  let zeros_val = const_int size_type 0
  let zerof_val = const_float float_type 0.
  let onei_val  = const_int int_type 1
  let ones_val  = const_int size_type 1
  let onef_val  = const_float float_type 1.

  (* attributes *)

  let inline_attr   = create_enum_attr g.context "inlinehint" 0L
  let always_inline = create_enum_attr g.context "alwaysinline" 0L
  let byval_attr    = create_enum_attr g.context "byval" 0L

  let set_inline func =
    add_function_attr func inline_attr AttrIndex.Function

  let set_always_inline func =
    add_function_attr func always_inline AttrIndex.Function

  let set_byval func i =
    add_function_attr func byval_attr (AttrIndex.Param i)

  let global_prefix = "gl."
  let global_name n = global_prefix ^ n

  let loc_var n = n ^ "."

  let gen_prefix = "gen."

  let lookup_lv (lv : lvenv) s i =
    begin match Lv.find lv i with
    | None        -> raise (CgLocalVarNotFound (s, i))
    | Some (n, v) -> n, v
    end

  let new_init () =
    let i = !(g.init_acc) in
    g.init_acc := i + 1;
    i

  let init_name i =
    Format.sprintf "init.%d" i

  let new_init_name () =
    let i = new_init () in
    init_name i

  let func_name n =
    if n = "init" then new_init_name ()
    else global_name n

  let get_str_lit s =
    match Pool.find g.str_pool s with
    | Some p -> p
    | None ->
       let p = build_global_stringptr s "pool.str" g.builder in
       Pool.add_exn g.str_pool ~key:s ~data:p;
       p

  let current_block () =
    insertion_block g.builder

  let current_func () =
    let b = current_block () in
    block_parent b

  let insert_block_after name b =
    let nb = insert_block g.context name b in
    move_block_after b nb;
    position_at_end nb g.builder;
    nb

  let insert_block_after_this name =
    insert_block_after name (current_block ())

  let new_block = insert_block_after_this

  let new_block_func name func =
    let b = append_block g.context name func in
    position_at_end b g.builder;
    b

  let with_this (f : llbasicblock -> 'a) : 'a =
    let this = insertion_block g.builder in
    let res  = f this in
    position_at_end this g.builder;
    res

  let recover_this (f : unit -> 'a) : 'a =
    with_this (fun _ -> f ())
    
  let jump_to_this b : unit =
    with_this (fun this ->
        position_at_end b g.builder;
        ignore (build_br this g.builder))

  let cond_branch cond sb ifb elb : unit =
    with_this (fun this ->
        position_at_end sb g.builder;
        ignore (build_cond_br cond ifb elb g.builder))

  (** if cond in sb { ifb }; this *)
  let if_cond_branch cond sb ifb : unit =
    with_this (fun this ->
        jump_to_this ifb;
        cond_branch cond sb ifb this)

  let ifelse_cond_branch cond sb ifb elb : unit =
    jump_to_this ifb;
    jump_to_this elb;
    cond_branch cond sb ifb elb

  let verify_func name func =
    if Llvm_analysis.verify_function func then
      ()
    else
      begin
        (* dump_module g.cgmod;
         * print_endline name.data;
         * flush stdout;
         * flush stderr; *)
        raise (BrokenFunction name)
      end

  let find_until_last_alloca func =
    let rec iter pos =
      match pos with
      | At_end bb -> builder_at_end g.context bb
      | Before ins
           when instr_opcode ins = Opcode.Alloca -> iter (instr_succ ins)
      | Before ins -> builder_before g.context ins in 
    iter (instr_begin (entry_block func))

  let append_alloca t =
    let func = current_func () in
    let builder = find_until_last_alloca func in
    build_alloca t "" builder

  let const_loop pref lim f =
    let bb    = current_block () in
    let predb = new_block (pref ^ "pred") in
    let bodyb = new_block (pref ^ "body") in
    let endb  = new_block (pref ^ "end") in

    position_at_end bb g.builder;
    ignore (build_br predb g.builder);

    position_at_end predb g.builder;
    let phi = build_phi [zeroi_val, bb] (pref ^ "idx") g.builder in
    let cmp = build_icmp Icmp.Slt phi lim "" g.builder in

    position_at_end bodyb g.builder;
    let r     = f phi in
    let cb    = current_block () in
    let nphi  = build_nsw_add phi onei_val "" g.builder in
    add_incoming (nphi, cb) phi;
    ignore (build_br predb g.builder);

    position_at_end predb g.builder;
    ignore (build_cond_br cmp bodyb endb g.builder);

    position_at_end endb g.builder;
    predb, cb, r

end
