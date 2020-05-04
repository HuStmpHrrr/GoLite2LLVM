open Syntax
open Typed
open Cg_common
open Meta

module Make (X : CgEnv) = struct
  open X
  open Basics (X)
  open Cg_expr.Make (X)
  open Cg_types.Make (X)
  open Cg_stmt.Make (X)
  open Cg_generate.Make (X)

  let codegen_func_decl name nts t lv =
    let ft   = func_type (List.map snd nts) t in
    let func = declare_function (func_name name) ft g.cgmod in

    let ps = params func in
    let m  = Lv.of_alist_reduce ~f:(fun x _ -> x)
                                (List.concat
                                   (List.mapi (fun i (n, t) ->
                                        match n.data with
                                        | Blank -> []
                                        | X x   ->
                                           let v = ps.(i) in
                                           set_value_name (fst (List.nth lv x)) v;
                                           [x, (v, t)]
                                      ) nts)) in
    List.iteri (fun i (_, t) ->
        if is_aggregate t then set_byval func i) nts;
    func, m
     
  let codegen_func_def name nts t lv ss =
    let func, m = codegen_func_decl name.data nts t lv in
    let bb      = new_block_func "entry" func in
    let lv'     = allocas lv (Lv.length m) in
    Lv.iteri m ~f:(fun ~key:i ~data:(v, t) ->
               if not (is_aggregate t) then
                 ignore (build_store v (snd (Lv.find_exn lv' i)) g.builder));
    if not (codegen_stmts lv' Out ss) then
      begin
        if t = Tvoid || is_aggregate t then
          ignore (build_ret_void g.builder)
        else
          ignore (build_unreachable g.builder)
      end;
    verify_func name func

  let codegen_gdecl (d : gdecl) : unit =
    match d with
    | VarDecl3 (_, nes, _)
      | VarDecl1 (_, nes) ->
       List.iter (fun (n, e) ->
           match n.data with
           | Blank -> ()
           | X x   ->
              let t = codegen_typ (get_typ e) in
              ignore (define_global (global_name x) (undef t) g.cgmod)) nes
    | VarDecl2 (_, ns, t) ->
       List.iter (fun n ->
           match n.data with
           | Blank -> ()
           | X x   ->
              let t = codegen_typ t in
              ignore (define_global (global_name x) (undef t) g.cgmod)) ns
    | TypDecl (_, _, _)   -> ()

  let codegen_top_decl (td : top_decl) : unit =
    match td with
    | DDecl gd                       -> codegen_gdecl gd
    | FunDecl (_, f, nts, t, lv, ss) ->
       match f.data with
       | Blank -> ()
       | X fn  -> codegen_func_def (update_data f fn) nts t lv ss

  let codegen_gname_binds nes : unit =
    let les = List.map (function
                        | ({ data = Blank }, _)     -> None
                        | ({ data = X s } as x , _) ->
                           Some (find_global_var (update_data x s))) nes in
    let res = List.map (fun (_, e) -> get_typ e, codegen_expr Lv.empty e) nes in
    batch_assign les res

  let codegen_main (tds : top_decl list) : unit =
    let rec init_gvars tds =
      match tds with
      | []       -> ()
      | DDecl (VarDecl3 (_, nes, _)
               | VarDecl1 (_, nes))
        :: tds   ->
         codegen_gname_binds nes;
         init_gvars tds
      | DDecl (VarDecl2 (_, ns, t))
        :: tds   ->
         List.iter (fun n ->
             match n.data with
             | Blank -> ()
             | X x   ->
                codegen_val_init (forget_data n) (find_global_var (update_data n x)) t) ns;
         init_gvars tds
      | _ :: tds -> init_gvars tds
    in

    let rec call_inits i =
      if i < !(g.init_acc) then
        begin
          let init_func = init_name i in
          ignore (build_call (match lookup_function init_func g.cgmod with
                              | None   -> raise (CgGlobalVarNotFound (meta_zero' init_func))
                              | Some v -> v) [| |] "" g.builder);
          call_inits (i + 1)
        end
    in

    let gen () =
      let func =
        declare_function "main" (function_type int_type [| |]) g.cgmod in
      let bb   = new_block_func "entry" func in
      init_gvars tds;
      call_inits 0;
      begin match lookup_function (global_name "main") g.cgmod with
      | None -> ()
      | Some f -> ignore (build_call f [| |] "" g.builder);
      end;

      ignore (build_ret zeroi_val g.builder);
      func
    in ignore (find_gen_func "main" gen)

end
