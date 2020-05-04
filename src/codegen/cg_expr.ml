open Syntax
open Typed
open Cg_common
open Conversion
open Meta

module Make (X : CgEnv) = struct
  open X
  open Basics (X)
  open Cg_types.Make (X)
  open Cg_generate.Make (X)

  (** how to assign the right value [r] of type [t] to a left value [l] *)
  let lr_assign l r t =
    if is_aggregate t then
      begin
        if l <> r then
          call_memcpy l r (codegen_typ t)
      end
    else
      ignore (build_store r l g.builder)

  let find_global_var x =
    match lookup_global (global_name x.data) g.cgmod with
    | None   ->
       raise (CgGlobalVarNotFound x)
    | Some v -> v

  let codegen_plus m t ce1 ce2 : llvalue =
    match t with
     | Tstr   -> call_strconcat ce1 ce2
     | Tint   -> build_nsw_add ce1 ce2 "int.add" g.builder
     | Tfloat -> build_fadd ce1 ce2 "fl.add" g.builder
     | Trune  -> build_nsw_add ce1 ce2 "rune.add" g.builder
     | _      -> raise (TcInconsistency (m, "cannot generate a plus instruction"))

  let codegen_minus m t ce1 ce2 : llvalue =
    match t with
     | Tint   -> build_nsw_sub ce1 ce2 "int.minus" g.builder
     | Tfloat -> build_fsub ce1 ce2 "fl.minus" g.builder
     | Trune  -> build_nsw_sub ce1 ce2 "rune.minus" g.builder
     | _      -> raise (TcInconsistency (m, "cannot generate a minus instruction"))

  let codegen_times m t ce1 ce2 : llvalue =
    match t with
     | Tint   -> build_nsw_mul ce1 ce2 "int.times" g.builder
     | Tfloat -> build_fmul ce1 ce2 "fl.times" g.builder
     | Trune  -> build_nsw_mul ce1 ce2 "rune.times" g.builder
     | _      -> raise (TcInconsistency (m, "cannot generate a times instruction"))

  let codegen_div m t ce1 ce2 : llvalue =
    match t with
     | Tint   -> build_sdiv ce1 ce2 "int.div" g.builder
     | Tfloat -> build_fdiv ce1 ce2 "fl.div" g.builder
     | Trune  -> build_sdiv ce1 ce2 "rune.div" g.builder
     | _      -> raise (TcInconsistency (m, "cannot generate a div instruction"))

  let codegen_rem m t ce1 ce2 : llvalue =
    match t with
     | Tint  -> build_srem ce1 ce2 "int.rem" g.builder
     | Trune -> build_srem ce1 ce2 "rune.rem" g.builder
     | _     -> raise (TcInconsistency (m, "cannot generate a rem instruction"))

  let codegen_band m t ce1 ce2 : llvalue =
    match t with
    | Tint  -> build_and ce1 ce2 "int.band" g.builder
    | Trune -> build_and ce1 ce2 "rune.band" g.builder
    | _     -> raise (TcInconsistency (m, "cannot generate a and instruction"))

  let codegen_bor m t ce1 ce2 : llvalue =
    match t with
    | Tint  -> build_or ce1 ce2 "int.or" g.builder
    | Trune -> build_or ce1 ce2 "rune.or" g.builder
    | _     -> raise (TcInconsistency (m, "cannot generate a or instruction"))

  let codegen_bxor m t ce1 ce2 : llvalue =
    match t with
    | Tint  -> build_xor ce1 ce2 "int.band" g.builder
    | Trune -> build_xor ce1 ce2 "rune.band" g.builder
    | _     -> raise (TcInconsistency (m, "cannot generate a xor instruction"))

  let codegen_bclear m t ce1 ce2 : llvalue =
    match t with
    | Tint   ->
       let nce2 = build_xor ce2 (m1_val int_type) "" g.builder in
       build_and ce1 nce2 "int.bclear" g.builder
    | Trune  ->
       let nce2 = build_xor ce2 (m1_val rune_type) "" g.builder in
       build_and ce1 nce2 "rune.bclear" g.builder
    | _      -> raise (TcInconsistency (m, "cannot generate a bit clear instruction"))

  let codegen_shift name build ce1 ce2 : llvalue =
    let func = current_func () in
    let bb   = current_block () in
    let cmp = build_icmp Icmp.Slt ce2 zeroi_val "" g.builder in

    let negb = new_block "negative-bits" in
    call_panic "shift by a negative number";

    let nnegb = new_block "nonnegative-bits" in
    cond_branch cmp bb negb nnegb;
    build ce1 ce2 name g.builder

  let codegen_lshift m t ce1 ce2 : llvalue =
    let name =
      match t with
      | Tint  -> "int.lshift"
      | Trune -> "rune.lshift"
      | _     -> raise (TcInconsistency (m, "cannot generate a left shift instruction"))
    in
    codegen_shift name build_shl ce1 ce2

  let codegen_rshift m t ce1 ce2 : llvalue =
    let name =
      match t with
      | Tint  -> "int.rshift"
      | Trune -> "rune.rshift"
      | _     -> raise (TcInconsistency (m, "cannot generate a right shift instruction"))
    in
    codegen_shift name build_ashr ce1 ce2

  (** v has to be a pointer value *)
  let expr_invariant v n t =
    if is_aggregate t then v
    else build_load v n g.builder

  let array_idx arr i lim =
    check_bound i lim "indexing out of bound for array";
    build_in_bounds_gep arr [| zeroi_val; i |] "" g.builder

  let slice_ptr s i t =
    let t'    = codegen_typ t in
    let elemp = build_struct_gep s 2 "" g.builder in
    let elem  = build_load elemp "" g.builder in
    let arr   = build_bitcast elem (pointer_type t') "" g.builder in
    build_in_bounds_gep arr [| i |] "" g.builder

  (** ce : slice*
   *  ci : int
   *)
  let slice_idx ce ci t =
    slice_check_bound ce ci;
    slice_ptr ce ci t

  (** invariance is
   *
   * e : t => [[ e ]] : [[ t ]]* if t is struct or array,
   * e : t => [[ e ]] : [[ t ]]  otherwise
   *)
  let rec codegen_expr lv (e : expr) : llvalue =
    match e with
    | GVar (x, t)           ->
       if is_func t then
         begin match lookup_function (global_name x.data) g.cgmod with
         | None   -> raise (CgGlobalVarNotFound x)
         | Some v -> v
         end
       else expr_invariant (find_global_var x) x.data t
    | LVar (s, i, t)        -> codegen_expr_lvar lv s i t
    | Int (k, s)            -> let i = Int64.of_int32 (to_int32 k s) in const_of_int64 int_type i true
    | Float (k, s)          -> let f = to_float k s in const_float float_type f
    | Bool b                -> if b.data = True then true_val else false_val
    | Rune (_, c)           -> const_int rune_type (Char.code c.data)
    | String (_, _, s)      -> get_str_lit s.data
    | App (_, f, es, t)     -> codegen_expr_funcall lv f es t
    | Append (_, e1, e2)    -> codegen_expr_append lv e1 e2
    | Cap (_, e)            -> codegen_expr_cap lv e
    | Len (_, e)            -> codegen_expr_len lv e
    | Cast (_, n, e, t)     -> codegen_expr_cast lv e t
    | Sel (_, e, i, f, t)   ->
       let ce = codegen_expr lv e in
       expr_invariant (build_struct_gep ce i "" g.builder) "sel" t
    | Idx (_, e, i, t)      -> codegen_expr_idx lv e i
    | Binop (op, e1, e2, t) ->
       begin match op.data with
       | Ar op' -> codegen_expr_arith lv (update_data op op') e1 e2
       | Lo op' -> codegen_expr_logic lv (update_data op op') e1 e2
       end
    | Uniop (op, e, _)      -> codegen_expr_uniop lv op.data e

  and codegen_expr_lvar lv s i t : llvalue =
    let n, v = lookup_lv lv s i in
    expr_invariant v (loc_var n) t

  and codegen_expr_funcall lv f es t : llvalue = 
    let cf  = codegen_expr lv f in
    let ces = Array.map (codegen_expr lv) (Array.of_list es) in
    if is_aggregate t then
      let ret = append_alloca (codegen_typ t) in
      ignore (build_call cf (Array.append ces [| ret |]) "" g.builder);
      ret
    else
      build_call cf ces "" g.builder

  and codegen_expr_append lv e1 e2 : llvalue =
    let ce1 = codegen_expr lv e1
    and ce2 = codegen_expr lv e2
    and t   = get_typ e2 in
    let s   = build_call (get_slice_augment ()) [| ce1 |] "append" g.builder in
    let len = build_call (get_slice_len ()) [| ce1 |] "" g.builder in
    let ip  = slice_ptr s len t in
    lr_assign ip ce2 t;
    s

  and codegen_expr_cap lv e : llvalue =
    match rt_expr e with
    | Tslice t      ->
       let cap = get_slice_cap ()
       and ce  = codegen_expr lv e in
       build_call cap [| ce |] "cap" g.builder
    | Tarray (i, _) -> const_of_int64 int_type (Int64.of_int32 i) true
    | _             -> raise (TcInconsistency (expr_meta e, "cannot codegen cap"))
       
  and codegen_expr_len lv e : llvalue =
    match rt_expr e with
    | Tstr          ->
       let strlen = strlen () in
       let ce     = codegen_expr lv e in
       let r      = build_call strlen [| ce |] "len" g.builder in
       build_trunc r int_type "" g.builder
    | Tslice t      ->
       let len = get_slice_len ()
       and ce  = codegen_expr lv e in
       build_call len [| ce |] "len" g.builder
    | Tarray (i, _) -> const_of_int64 int_type (Int64.of_int32 i) true
    | _             -> raise (TcInconsistency (expr_meta e, "cannot codegen cap"))

  and codegen_expr_cast lv e t : llvalue =
    let ce = codegen_expr lv e in
    match resolved_typ t, rt_expr e with
    | t, t'
         when t === t' -> ce
    | Trune , Tint     -> ce
    | Tfloat, Tint     -> build_sitofp ce float_type "cast" g.builder
    | Tint  , Trune    -> ce
    | Tfloat, Trune    -> build_sitofp ce float_type "cast" g.builder
    | (Tint | Trune)
            , Tfloat   -> build_fptosi ce int_type "cast" g.builder
    | Tstr  , Tint     -> call_r2s ce
    | Tstr  , Trune    -> call_r2s ce
    | _, _             -> raise (TcInconsistency (expr_meta e, "cannot codegen cast"))

  and codegen_expr_idx lv e i : llvalue =
    let ce = codegen_expr lv e
    and ci = codegen_expr lv i in
    match rt_expr e with
    | Tarray (s, t) ->
       let b = const_of_int64 int_type (Int64.of_int32 s) true in
       let r = array_idx ce ci b in
       expr_invariant r "idx" t
    | Tslice t      -> expr_invariant (slice_idx ce ci t) "idx" t
    | _             -> raise (TcInconsistency (expr_meta e, "cannot codegen indexing"))

  and codegen_expr_logic lv op e1 e2 : llvalue =
    match op.data with
     | And -> codegen_expr_and lv e1 e2
     | Or  -> codegen_expr_or lv e1 e2
     | _ ->
        let ce1 = codegen_expr lv e1
        and ce2 = codegen_expr lv e2
        and t   = rt_expr e1 in
        match op.data with
        | Eq  -> codegen_expr_eq (forget_data op) t ce1 ce2
        | Neq ->
           let r = codegen_expr_eq (forget_data op) (get_typ e1) ce1 ce2 in
           build_not r "neq" g.builder
        | Ge  -> codegen_expr_ge (forget_data op) t ce1 ce2
        | Le  -> codegen_expr_le (forget_data op) t ce1 ce2
        | Gt  -> codegen_expr_gt (forget_data op) t ce1 ce2
        | Lt  -> codegen_expr_lt (forget_data op) t ce1 ce2
        | _   -> raise Utils.Impossible
    
  and codegen_expr_or lv e1 e2 : llvalue =
    let ce1      = codegen_expr lv e1 in
    let start_bb = current_block () in
    let func     = block_parent start_bb in

    (* the basic block for the case where e1 evaluates to false *)
    let false_bb = new_block "or.false" in
    let ce2    = codegen_expr lv e2 in
    let ce2_bb = current_block () in

    (* the basic block where the evaluation has finished *)
    let res_bb = new_block "or.res" in
    (* phi node. if jump from start_bb then it's true, otherwise it's ce2 *)
    let phi    = build_phi [(true_val, start_bb); (ce2, ce2_bb)] "or" g.builder in

    (* insert a jump at the end of false_bb *)
    jump_to_this false_bb;
    (* insert a conditional jump at the end of start_bb *)
    cond_branch ce1 start_bb res_bb false_bb;
    phi
    
  and codegen_expr_and lv e1 e2 : llvalue =
    let ce1      = codegen_expr lv e1 in
    let start_bb = current_block () in
    let func     = block_parent start_bb in

    let true_bb = new_block "and.true" in
    let ce2     = codegen_expr lv e2 in
    let ce2_bb  = current_block () in

    let res_bb = new_block "and.res" in
    let phi    = build_phi [(false_val, start_bb); (ce2, ce2_bb)] "and" g.builder in

    if_cond_branch ce1 start_bb true_bb;
    phi

  (** note that the t here is not resolved. it's quite important for generated comparison *)
  and codegen_expr_eq m t ce1 ce2 : llvalue =
    match resolved_typ t with
    | Tbool
      | Trune
      | Tint        -> build_icmp Icmp.Eq ce1 ce2 "eq" g.builder
    | Tfloat        -> build_fcmp Fcmp.Oeq ce1 ce2 "float.eq" g.builder
    | Tstr          ->
       let cmp = build_call (strcmp ()) [| ce1; ce2 |] "" g.builder in
       build_icmp Icmp.Eq cmp zeroi_val "str.eq" g.builder
    | Tarray (i, t) ->
       let predb, cb, incmp =
         const_loop "arr.eq." (const_of_int64 int_type (Int64.of_int32 i) true)
                    (fun phi ->
                      let cep1  = build_in_bounds_gep ce1 [| zeroi_val; phi |] "" g.builder in
                      let cep2  = build_in_bounds_gep ce2 [| zeroi_val; phi |] "" g.builder in
                      let v1    = expr_invariant cep1 "" t in
                      let v2    = expr_invariant cep2 "" t in
                      let incmp = codegen_expr_eq m t v1 v2 in
                      incmp) in
       let endb = current_block () in

       position_at_end cb g.builder;
       begin match instr_end cb with
       | At_start _ -> ()
       | After i    -> delete_instruction i
       end;
       ignore (build_cond_br incmp predb endb g.builder);

       position_at_end endb g.builder;
       build_phi [(true_val, predb); (false_val, cb)] "arr.eq" g.builder
       
    | Tstruct _     ->
       let func = codegen_expr_eq_func m t in
       build_call func [| ce1; ce2 |] "struct.eq" g.builder
    | _             -> raise (TcInconsistency (m, "cannot generate eq instruction"))

  (** generate a function to compare ce1 and ce2 which have a struct type t *)
  and codegen_expr_eq_func m t : llvalue =
    let eq_func_name = gen_prefix ^ "eq." ^ encode_typ t in
    let param_type   = param_typ t in
    match resolved_typ t with
    | Tstruct fs ->
       let gen () =
         let func =
           declare_function eq_func_name
                            (function_type bool_type [| param_type; param_type |])
                            g.cgmod in
         let bb   = new_block_func "entry" func in
         let ptr1 = param func 0
         and ptr2 = param func 1 in

         position_at_end bb g.builder;
         List.iteri (fun i (_, ft) ->
             let fp1 = build_struct_gep ptr1 i "" g.builder in
             let fp2 = build_struct_gep ptr2 i "" g.builder in
             let v1  = expr_invariant fp1 "" ft in
             let v2  = expr_invariant fp2 "" ft in
             let cmp = codegen_expr_eq m ft v1 v2 in
             let cbb = current_block () in

             let rb  = new_block "struct.eq.ret" in
             ignore (build_ret false_val g.builder);

             let nb  = new_block "struct.eq.next" in
             cond_branch cmp cbb nb rb
           ) fs;
         ignore (build_ret true_val g.builder);
         func
       in
       find_gen_func eq_func_name gen
    | _          -> raise (TcInconsistency (m, "wrong resolved type for eq comparison when treated as a struct"))

  and codegen_expr_ge m t ce1 ce2 : llvalue =
    match t with
    | Trune
      | Tint -> build_icmp Icmp.Sge ce1 ce2 "ge" g.builder
    | Tfloat -> build_fcmp Fcmp.Oge ce1 ce2 "float.ge" g.builder
    | Tstr   ->
       let cmp = build_call (strcmp ()) [| ce1; ce2 |] "" g.builder in
       build_icmp Icmp.Sge cmp zeroi_val "str.ge" g.builder
    | _      -> raise (TcInconsistency (m, "cannot generate ge instruction"))

  and codegen_expr_gt m t ce1 ce2 : llvalue =
    match t with
    | Trune
      | Tint -> build_icmp Icmp.Sgt ce1 ce2 "gt" g.builder
    | Tfloat -> build_fcmp Fcmp.Ogt ce1 ce2 "float.gt" g.builder
    | Tstr   ->
       let cmp = build_call (strcmp ()) [| ce1; ce2 |] "" g.builder in
       build_icmp Icmp.Sgt cmp zeroi_val "str.gt" g.builder
    | _      -> raise (TcInconsistency (m, "cannot gtnerate gt instruction"))

  and codegen_expr_le m t ce1 ce2 : llvalue =
    match t with
    | Trune
      | Tint -> build_icmp Icmp.Sle ce1 ce2 "le" g.builder
    | Tfloat -> build_fcmp Fcmp.Ole ce1 ce2 "float.le" g.builder
    | Tstr   ->
       let cmp = build_call (strcmp ()) [| ce1; ce2 |] "" g.builder in
       build_icmp Icmp.Sle cmp zeroi_val "str.le" g.builder
    | _      -> raise (TcInconsistency (m, "cannot lenerate le instruction"))

  and codegen_expr_lt m t ce1 ce2 : llvalue =
    match t with
    | Trune
      | Tint -> build_icmp Icmp.Slt ce1 ce2 "lt" g.builder
    | Tfloat -> build_fcmp Fcmp.Olt ce1 ce2 "float.lt" g.builder
    | Tstr   ->
       let cmp = build_call (strcmp ()) [| ce1; ce2 |] "" g.builder in
       build_icmp Icmp.Slt cmp zeroi_val "str.lt" g.builder
    | _      -> raise (TcInconsistency (m, "cannot ltnerate lt instruction"))

  and codegen_expr_uniop lv op e : llvalue = 
    let ce = codegen_expr lv e in
    match op with
    | Pos   -> ce
    | Neg   ->
       begin match rt_expr e with
       | Tfloat -> build_fneg ce "neg" g.builder
       | _      -> build_neg ce "neg" g.builder
       end
    | Not   -> build_not ce "not" g.builder
    | Bcomp ->
       (* xor -1 is one's complement *)
       build_xor ce (m1_val (codegen_typ (rt_expr e))) "comp" g.builder

  and codegen_expr_arith lv op e1 e2 : llvalue =
    let ce1 = codegen_expr lv e1
    and ce2 = codegen_expr lv e2
    and m   = expr_meta e1
    and t   = rt_expr e1 in
    codegen_expr_arith_code t op ce1 ce2

  and codegen_expr_arith_code t op ce1 ce2 =
    let m = forget_data op in
    match op.data with
    | Plus   -> codegen_plus m t ce1 ce2
    | Minus  -> codegen_minus m t ce1 ce2
    | Times  -> codegen_times m t ce1 ce2
    | Div    -> codegen_div m t ce1 ce2
    | Rem    -> codegen_rem m t ce1 ce2
    | Band   -> codegen_band m t ce1 ce2
    | Bor    -> codegen_bor m t ce1 ce2
    | Bxor   -> codegen_bxor m t ce1 ce2
    | Lshift -> codegen_lshift m t ce1 ce2
    | Rshift -> codegen_rshift m t ce1 ce2
    | Bclear -> codegen_bclear m t ce1 ce2

  (* an aexpr compile to a left value (namely an address) *)
  let rec codegen_aexpr_l lv e : llvalue =
    match e with
    | AGVar (x, _)         ->
       begin match lookup_global (global_name x.data) g.cgmod with
       | None   -> raise (CgGlobalVarNotFound x)
       | Some v -> v
       end
    | ALVar (s, i, _)      -> snd (lookup_lv lv s i)
    | ASel (_, e, i, f, _) ->
       let ce = codegen_aexpr_l lv e in
       build_struct_gep ce i "l.sel" g.builder
    | AIdx (_, e, i, _)    ->
       let ce = codegen_aexpr_l lv e in
       let ci = codegen_expr lv i in
       match resolved_typ (get_atyp e) with
       | Tarray (s, _) ->
          let b = const_of_int64 int_type (Int64.of_int32 s) true in
          array_idx ce ci b
       | Tslice t      ->
          let ce = build_load ce "" g.builder in
          slice_idx ce ci t
       | _             -> raise (TcInconsistency (aexpr_meta e, "cannot codegen indexing"))


  (* an aexpr compile to left and right values at the same time *)
  let codegen_aexpr_lr lv e : llvalue * llvalue =
    let l = codegen_aexpr_l lv e in
    let r = build_load l "" g.builder in
    l, r

  let codegen_lexpr lv e : llvalue option =
    match e with
    | LBlank _ -> None
    | LAexpr e -> Some (codegen_aexpr_l lv e)

  let rec codegen_val_init m l t : unit =
    match resolved_typ t with
    | Tstr          -> ignore (build_store (get_str_lit "") l g.builder)
    | Tint          -> ignore (build_store zeroi_val l g.builder)
    | Tfloat        -> ignore (build_store zerof_val l g.builder)
    | Trune         -> ignore (build_store zeroi_val l g.builder)
    | Tbool         -> ignore (build_store false_val l g.builder)
    | Tslice t      ->
       let nsf = get_new_slice () in
       let ns  = build_call nsf [| size_of (codegen_typ t) |] "" g.builder in
       ignore (build_store ns l g.builder)
    | Tarray (i, t) ->
       ignore (const_loop "valinit."
                          (const_of_int64 int_type (Int64.of_int32 i) true)
                          (fun idx ->
                            let p = build_in_bounds_gep l  [| zeroi_val; idx |] "" g.builder in
                            codegen_val_init m p t))
    | Tstruct _     ->
       let init_func = codegen_val_init_struct_func m t in
       ignore (build_call init_func [| l |] "" g.builder)
    | _             -> raise (TcInconsistency (m, "void and function should not need to be initialized"))

  and codegen_val_init_struct_func m t : llvalue =
    let init_func_name = gen_prefix ^ "valinit." ^ encode_typ t in
    let param_type     = param_typ t in
    match resolved_typ t with
    | Tstruct fs ->
       let gen () =
         let func =
           declare_function init_func_name
                            (function_type void_type [| param_type |])
                            g.cgmod in
         let bb   = new_block_func "entry" func in
         let ptr  = param func 0 in
         
         List.iteri (fun i (_, ft) ->
             let fp = build_struct_gep ptr i "" g.builder in
             codegen_val_init m fp ft
           ) fs;
         ignore (build_ret_void g.builder);
         func
       in
       find_gen_func init_func_name gen
    | _          -> raise (TcInconsistency (m, "wrong resolved type for value initialization when treated as a struct"))

end
