open Syntax
open Typed
open Cg_common
open Meta

module Make (X : CgEnv) = struct
  open X
  open Basics (X)

  let struct_file_name   = "struct._IO_FILE"
  let struct_marker_name = "struct._IO_marker"

  let file_io_structs () =
    match type_by_name g.cgmod struct_file_name,
          type_by_name g.cgmod struct_marker_name with
    | Some t, Some t' -> t, t'
    | _     , _       ->
       let file = named_struct_type g.context struct_file_name in
       let marker = named_struct_type g.context struct_marker_name in
       let i8 = i8_type g.context in
       let i8p = pointer_type i8 in
       struct_set_body file [|
                         int_type;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         pointer_type marker;
                         pointer_type file;
                         int_type;
                         int_type;
                         size_type;
                         i16_type g.context;
                         i8;
                         array_type i8 1;
                         i8p;
                         i64_type g.context;
                         i8p;
                         i8p;
                         i8p;
                         i8p;
                         size_type;
                         int_type;
                         array_type i8 (if Sys.word_size = 32 then 40 else 20);
                       |] false;
       struct_set_body marker [|
                         pointer_type marker;
                         pointer_type file;
                         int_type
                       |] false;
       file, marker

  let struct_file () = fst (file_io_structs ())

  let filep () = pointer_type (struct_file ())

  let stderr () =
    match lookup_global "stderr" g.cgmod with
    | Some v -> v
    | None   ->
       let v = declare_global (filep ()) "stderr" g.cgmod in
       set_linkage Linkage.External v;
       v

  let stdout () =
    match lookup_global "stdout" g.cgmod with
    | Some v -> v
    | None   ->
       let v = declare_global (filep ()) "stdout" g.cgmod in
       set_linkage Linkage.External v;
       v

  let find_c_func name t =
    match lookup_function name g.cgmod with
    | Some f -> f
    | None   -> declare_function name t g.cgmod

  let find_gen_func name gen =
    match lookup_function name g.cgmod with
    | Some f -> f
    | None   -> recover_this (fun () ->
                    let f = gen () in
                    verify_func (meta_zero' name) f;
                    f)

  let fprintf () =
    find_c_func "fprintf" (var_arg_function_type int_type [| filep (); str_type |])

  let snprintf () =
    find_c_func "snprintf" (var_arg_function_type size_type [| str_type; size_type; str_type |])

  let sprintf () =
    find_c_func "sprintf" (var_arg_function_type size_type [| str_type; str_type |])

  let cexit () =
    find_c_func "exit" (function_type void_type [| int_type |])

  let strlen () =
    find_c_func "strlen" (function_type size_type [| str_type |])

  let call_strlen s =
    build_call (strlen ()) [| s |] "" g.builder

  let strcmp () =
    find_c_func "strcmp" (function_type int_type [| str_type; str_type |])

  let memcpy () =
    find_c_func "memcpy" (function_type voidp_type [| voidp_type; voidp_type; size_type |])

  let malloc () =
    find_c_func "malloc" (function_type voidp_type [| size_type |])

  let call_memcpy pd ps t' =
    let ud = build_bitcast pd (voidp_type) "" g.builder in
    let us = build_bitcast ps (voidp_type) "" g.builder in
    ignore (build_call (memcpy ()) [| ud; us; size_of t' |] "" g.builder)

  let panic_name = gen_prefix ^ "panic"

  let panic () =
    let gen () =
      let func = declare_function panic_name (function_type void_type [| str_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s    = param func 0 in
      let serr = build_load (stderr ()) "" g.builder in
      let pstr = get_str_lit "Error: %s" in
      ignore (build_call (fprintf ()) [| serr; pstr; s |] "" g.builder);
      ignore (build_call (cexit ()) [| const_int int_type 1 |] "" g.builder);
      ignore (build_unreachable g.builder);
      func
    in
    find_gen_func panic_name gen

  let call_panic s =
    let pf = panic ()
    and sp = get_str_lit s in
    ignore (build_call pf [| sp |] "" g.builder);
    ignore (build_unreachable g.builder)

  let build_array_malloc t n s builder =
    let bytes = build_mul (size_of t) n "" builder in
    let size  = build_intcast bytes size_type "" builder in
    let ptr   = build_call (malloc ()) [| size |] "" builder in
    build_bitcast ptr (pointer_type t) s builder

  let call_mallocs t n s =
    let func   = current_func ()
    and bb     = current_block ()
    and memp   = build_array_malloc t n "" g.builder in
    let isnull = build_is_null memp "" g.builder in

    let nullb = new_block "isnull" in
    call_panic s;

    (* here malloc is sucessful *)
    let notnullb = new_block "notnull" in
    cond_branch isnull bb nullb notnullb;
    memp

  let call_malloc t s = call_mallocs t onei_val s

  let bound_check_name = gen_prefix ^ "bound_check"

  let bound_check () =
    let gen () =
      let func = declare_function bound_check_name
                                  (function_type void_type [| int_type; int_type ; str_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let idx  = param func 0
      and lim  = param func 1
      and msg  = param func 2 in
      let cmp  = build_icmp Icmp.Slt idx lim "" g.builder in

      let oob = new_block "out-of-bound" in
      let pf  = panic () in
      ignore (build_call pf [| msg |] "" g.builder);
      ignore (build_unreachable g.builder);

      let ib = new_block "in-bound" in
      cond_branch cmp bb ib oob;
      ignore (build_ret_void g.builder);

      (* hint that the function can be inlined *)
      set_inline func;
      func
    in find_gen_func bound_check_name gen

  let check_bound i lim s : unit =
    let sp = get_str_lit s in
    let fp = bound_check () in
    ignore (build_call fp [| i; lim; sp |] "" g.builder)

  let int_to_string_name = gen_prefix ^ "int_to_string"

  let int_to_string () =
    let gen () =
      let func = declare_function int_to_string_name
                                  (function_type str_type [| int_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let i    = param func 0 in
      let fmt  = get_str_lit "%d" in
      let sz   = build_call (snprintf ()) [| const_null str_type; zeros_val; fmt; i |] "" g.builder in
      let szp1 = build_nsw_add sz ones_val "" g.builder in
      let buf  = call_mallocs i8 szp1 "to string malloc failed" in
      ignore (build_call (sprintf ()) [| buf; fmt; i |] "" g.builder);
      ignore (build_ret buf g.builder);
      func
    in find_gen_func int_to_string_name gen

  let call_i2s i =
    build_call (int_to_string ()) [| i |] "" g.builder

  let float_to_string_name = gen_prefix ^ "float_to_string"

  let float_to_string () =
    let gen () =
      let func = declare_function float_to_string_name
                                  (function_type str_type [| float_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let f    = param func 0 in
      let fmt  = get_str_lit "%f" in
      let sz   = build_call (snprintf ()) [| const_null str_type; zeros_val; fmt; f |] "" g.builder in
      (* +1 for \0 *)
      let szp1 = build_nsw_add sz ones_val "" g.builder in
      let buf  = call_mallocs i8 szp1 "to string malloc failed" in
      ignore (build_call (sprintf ()) [| buf; fmt; f |] "" g.builder);
      ignore (build_ret buf g.builder);
      func
    in find_gen_func float_to_string_name gen

  let call_f2s f =
    build_call (float_to_string ()) [| f |] "" g.builder

  let rune_to_string_name = gen_prefix ^ "rune_to_string"

  let rune_to_string () =
    let gen () =
      let func = declare_function rune_to_string_name
                                  (function_type str_type [| rune_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let c    = param func 0 in
      let fmt  = get_str_lit "%c" in
      let buf  = call_mallocs i8 (const_int size_type 2) "to string malloc failed" in
      ignore (build_call (sprintf ()) [| buf; fmt; c |] "" g.builder);
      ignore (build_ret buf g.builder);
      func
    in find_gen_func rune_to_string_name gen

  let call_r2s c =
    build_call (rune_to_string ()) [| c |] "" g.builder

  let strconcat_name = gen_prefix ^ "strconcat"

  let strconcat () =
    let gen () =
      let func = declare_function strconcat_name
                                  (function_type str_type [| str_type; str_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s1   = param func 0
      and s2 = param func 1 in
      let szs1 = call_strlen s1
      and szs2 = call_strlen s2 in
      let sz12 = build_nsw_add szs1 szs2 "" g.builder in
      let szp1 = build_nsw_add sz12 ones_val "" g.builder in
      let buf  = call_mallocs i8 szp1 "strconcat malloc failed" in
      let fmt = get_str_lit "%s%s" in
      ignore (build_call (sprintf ()) [| buf; fmt; s1; s2 |] "" g.builder);
      ignore (build_ret buf g.builder);
      func
    in find_gen_func strconcat_name gen

  let call_strconcat s1 s2 =
    build_call (strconcat ()) [| s1; s2 |] "" g.builder

  (* slice related code *)

  let slice_name = gen_prefix ^ "slice"

  let slice_struct_type () =
    match type_by_name g.cgmod slice_name with
    | Some t -> t
    | None   ->
       let s = named_struct_type g.context slice_name in
       struct_set_body s [|
                         int_type;   (* cap *)
                         int_type;   (* len *)
                         bytep_type; (* array *)
                         size_type   (* element size *)
                       |] false;
       s

  let slice_type () = pointer_type (slice_struct_type ())

  let seth_slice_cap s i =
    let capp = build_struct_gep s 0 "" g.builder in
    ignore (build_store i capp g.builder)

  let geth_slice_cap s =
    let capp = build_struct_gep s 0 "" g.builder in
    build_load capp "" g.builder

  let seth_slice_len s i =
    let lenp = build_struct_gep s 1 "" g.builder in
    ignore (build_store i lenp g.builder)

  let geth_slice_len s =
    let lenp = build_struct_gep s 1 "" g.builder in
    build_load lenp "" g.builder

  let seth_slice_elems s es =
    let elemsp = build_struct_gep s 2 "" g.builder in
    ignore (build_store es elemsp g.builder)

  let geth_slice_elems s =
    let elemsp = build_struct_gep s 2 "" g.builder in
    build_load elemsp "" g.builder

  let seth_slice_elem_size s i =
    let bufsizep = build_struct_gep s 3 "" g.builder in
    ignore (build_store i bufsizep g.builder)

  let geth_slice_elem_size s =
    let bufsizep = build_struct_gep s 3 "" g.builder in
    build_load bufsizep "" g.builder

  let slice_cap_name = gen_prefix ^ "slice_cap"

  let get_slice_cap () =
    let gen () =
      let func =
        declare_function slice_cap_name (function_type int_type [| slice_type () |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s    = param func 0 in
      let cap  = geth_slice_cap s in
      ignore (build_ret cap g.builder);
      
      (* hint that the function should be inlined *)
      set_always_inline func;
      func
    in find_gen_func slice_cap_name gen
     

  let slice_len_name = gen_prefix ^ "slice_len"

  let get_slice_len () =
    let gen () =
      let func =
        declare_function slice_len_name (function_type int_type [| slice_type () |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s    = param func 0 in
      let len  = geth_slice_len s in
      ignore (build_ret len g.builder);

      (* hint that the function should be inlined *)
      set_always_inline func;
      func
    in find_gen_func slice_len_name gen

  let slice_bound_check_name = gen_prefix ^ "slice_bound_check"

  let slice_bound_check () =
    let gen () =
      let func = declare_function slice_bound_check_name
                                  (function_type void_type [| slice_type (); int_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s    = param func 0
      and i    = param func 1 in
      let len  = geth_slice_len s in
      check_bound i len "indexing out of bound for slice";
      ignore (build_ret_void g.builder);

      (* hint that the function can be inlined *)
      set_inline func;
      func
    in find_gen_func slice_bound_check_name gen

  let slice_check_bound s i =
    ignore (build_call (slice_bound_check ()) [| s; i |] "" g.builder)

  let slice_malloc_msg = "memory allocation failure for a slice"
  let slice_elems_malloc_msg = "memory allocation failure for a slice element array"

  let new_slice_name = gen_prefix ^ "new_slice"

  let get_new_slice () =
    let gen () =
      let func =
        declare_function new_slice_name (function_type (slice_type ()) [| size_type |]) g.cgmod in
      let bb   = new_block_func "entry" func in

      (* malloc for slice *)
      let slicep   = call_malloc (slice_struct_type ()) slice_malloc_msg
      and notnullb = current_block ()
      and size     = param func 0 in

      seth_slice_cap slicep zeroi_val;
      seth_slice_len slicep zeroi_val;
      seth_slice_elems slicep (const_null str_type);
      seth_slice_elem_size slicep size;
      
      ignore (build_ret slicep g.builder);
      func
    in find_gen_func new_slice_name gen

  let slice_augment_name = gen_prefix ^ "slice_augment"

  let get_slice_augment () =
    let gen () =
      let func =
        declare_function slice_augment_name (function_type (slice_type ()) [| slice_type () |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      let s    = param func 0 in
      let cap  = geth_slice_cap s in
      let len  = geth_slice_len s in
      let buf  = geth_slice_elems s in
      let esz  = geth_slice_elem_size s in
      let cmp  = build_icmp Icmp.Slt len cap "" g.builder in

      let icb  = new_block "in-cap" in
      let sl1  = call_malloc (slice_struct_type ()) slice_malloc_msg in
      seth_slice_cap sl1 cap;
      seth_slice_len sl1 len;
      seth_slice_elems sl1 buf;
      seth_slice_elem_size sl1 esz;
      let icb' = current_block () in

      let ocb    = new_block "out-of-cap" in
      let sl2    = call_malloc (slice_struct_type ()) slice_malloc_msg in
      seth_slice_len sl2 len;
      seth_slice_elem_size sl2 esz;
      let isnull = build_is_null buf "" g.builder in
      let ocb'   = current_block () in

      let nullb  = new_block "buf-null" in
      seth_slice_cap sl2 (const_int int_type 2);
      let nbuf   = call_mallocs i8 (build_mul esz (const_int size_type 2) "" g.builder)
                                slice_elems_malloc_msg in
      seth_slice_elems sl2 nbuf;
      let nullb' = current_block () in

      let nnullb = new_block "buf-notnull" in
      let cap2   = build_mul cap (const_int int_type 2) "" g.builder in
      seth_slice_cap sl2 cap2;
      let bytes  = build_mul esz (build_intcast cap size_type "" g.builder) "" g.builder in
      let bytes2 = build_mul bytes (const_int size_type 2) "" g.builder in
      let newbuf = call_mallocs i8 bytes2 slice_elems_malloc_msg in
      ignore (build_call (memcpy ()) [| newbuf; buf; bytes |] "" g.builder);
      seth_slice_elems sl2 newbuf;
      let nnb'   = current_block () in

      let mgb = new_block "merge" in
      jump_to_this icb';
      jump_to_this nullb';
      jump_to_this nnb';
      cond_branch cmp bb icb ocb;
      cond_branch isnull ocb' nullb nnullb;
      let phi = build_phi [sl1, icb'; sl2, nullb'; sl2, nnb'] "" g.builder in
      seth_slice_len phi (build_nsw_add (geth_slice_len phi) onei_val "" g.builder);

      ignore (build_ret phi g.builder);
      func
    in find_gen_func slice_augment_name gen
     
end
