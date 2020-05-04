open Syntax
open Typed
open Cg_common
open Meta

module Make (X : CgEnv) = struct
  open X
  open Basics (X)
  open Cg_types.Make (X)
  open Cg_expr.Make (X)
  open Cg_generate.Make (X)

  type status =
    | Inloop         of llbasicblock * llbasicblock
    | Inswitch       of llbasicblock
    | InswitchInloop of llbasicblock * llbasicblock
    | Out

  let batch_assign les res =
    List.iter2 (function
                | None   -> fun _ -> ()
                | Some l -> fun (t, r) -> lr_assign l r t) les res

  let codegen_assign lv nes : unit =
    let les = List.map (fun (e, _) -> codegen_lexpr lv e) nes
    and res = List.map (fun (_, e) -> get_typ e, codegen_expr lv e) nes in
    batch_assign les res

  let codegen_simp_stmt lv (s : simp_stmt) : unit =
    match s with
    | Nop _                  -> ()
    | FApp (_, f, es, t)     -> ignore (codegen_expr_funcall lv f es t)
    | Incr e                 ->
       let addr, ce = codegen_aexpr_lr lv e.data in
       let ce2      =
         match resolved_typ (get_atyp e.data) with
         | Tfloat -> build_fadd ce onef_val "incr" g.builder
         | (Trune | Tint)
           as t   -> build_nsw_add ce (const_int (codegen_typ t) 1) "incr" g.builder
         | _      -> raise (TcInconsistency (aexpr_meta e.data, "cannot codegen incr")) in
       ignore (build_store ce2 addr g.builder)
    | Decr e                 ->
       let addr, ce = codegen_aexpr_lr lv e.data in
       let ce2      =
         match resolved_typ (get_atyp e.data) with
         | Tfloat -> build_fsub ce onef_val "decr" g.builder
         | (Trune | Tint)
           as t   -> build_nsw_sub ce (const_int (codegen_typ t) 1) "decr" g.builder
         | _      -> raise (TcInconsistency (aexpr_meta e.data, "cannot codegen incr")) in
       ignore (build_store ce2 addr g.builder)
    | Assign (_, nes)        -> codegen_assign lv nes
    | AssignOp (m, l, op, r) ->
       let al, cl = codegen_aexpr_lr lv l
       and cr = codegen_expr lv r in
       let ce = codegen_expr_arith_code (get_atyp l) (update_data m op) cl cr in
       ignore (build_store ce al g.builder)
    | ShortDecl (_, nes)     ->
       let res = List.map (fun (_, e) -> get_typ e, codegen_expr lv e) nes in
       let les = List.map (fun (n, _) ->
                     match n.data with
                     | SBlank  -> None
                     | Existed i
                       | New i -> Some (snd (Lv.find_exn lv i))) nes in
       batch_assign les res

  let codegen_lname_binds lv nes : unit =
    let les = List.map (function
                        | ({ data = Blank }, _) -> None
                        | ({ data = X i }  , _) -> Some (snd (Lv.find_exn lv i))) nes in
    let res = List.map (fun (_, e) -> get_typ e, codegen_expr lv e) nes in
    batch_assign les res

  let codegen_ldecl lv (d : ldecl) : unit =
    match d with
    | VarDecl1 (_, nes)    -> codegen_lname_binds lv nes
    | VarDecl2 (_, ns, t)  ->
       List.iter (fun n ->
           match n.data with
           | Blank -> ()
           | X x   -> codegen_val_init (forget_data n) (snd (Lv.find_exn lv x)) t) ns
    | VarDecl3 (_, nes, _) -> codegen_lname_binds lv nes
    | TypDecl (_, _, _)    -> ()

  (** return whether the statement has returned *)
  let rec codegen_stmt lv (st : status) (s : stmt) : bool =
    match s with
     | Simpl s                   -> codegen_simp_stmt lv s; false
     | Decl d                    -> codegen_ldecl lv d; false
     | Block ss                  -> codegen_stmts lv st ss
     | Print es                  ->
        let fmts, ces = codegen_stmt_print_helper lv es.data in
        let fmt       = get_str_lit (String.concat "" fmts) in
        let sout      = build_load (stdout ()) "" g.builder in
        ignore (build_call (fprintf ()) (Array.of_list (sout :: fmt :: ces)) "" g.builder);
        false
     | Println es                ->
        let fmts, ces = codegen_stmt_print_helper lv es.data in
        let fmt       = get_str_lit ((String.concat " " fmts) ^ "\n") in
        let sout      = build_load (stdout ()) "" g.builder in
        ignore (build_call (fprintf ()) (Array.of_list (sout :: fmt :: ces)) "" g.builder);
        false

     | Return e                  ->
        begin match e.data with
        | None                   -> ignore (build_ret_void g.builder)
        | Some e                 ->
           let t  = get_typ e
           and ce = codegen_expr lv e in
           if is_aggregate t then
             let t' = codegen_typ t in
             let ps = params (current_func ()) in
             let p  = ps.(Array.length ps - 1) in
             begin
               if p <> ce then
                 call_memcpy p ce t';
               ignore (build_ret_void g.builder)
             end
           else
             ignore (build_ret ce g.builder)
        end;
        true

     | If (_, b, e, ifs, els)    ->
        codegen_simp_stmt lv b;
        let func = current_func ()
        and pred = codegen_expr lv e
        and bb   = current_block () in

        let tr     = new_block "if.true" in
        let tr_end = codegen_stmts lv st ifs in
        let tr'    = current_block () in

        begin match els with
        (* there is no else block *)
        | None ->
           let ifend = new_block "if.end" in
           (* if the tr block has no termating instruction, like ret or br, we need to
              add one, otherwise, we shouldn't do anything *)
           if not tr_end then
             jump_to_this tr';
           cond_branch pred bb tr ifend;

        (* there is an else block *)
        | Some els ->
           let fls    = new_block "if.false" in
           let fl_end = codegen_stmts lv st els in
           let fls'  = current_block () in

           let ifend = new_block "if.end" in
           (* the same logic as above *)
           if not tr_end then
             jump_to_this tr';
           if not fl_end then
             jump_to_this fls';
           cond_branch pred bb tr fls;
        end;
        false

     | Switch (_, b, e, cs, dfl) ->
        codegen_simp_stmt lv b;
        let func = current_func ()
        and ce   = codegen_expr lv e
        and bb   = current_block () in

        let blocks = List.map (fun _ -> new_block "switch.case") cs
        and dflb   = Option.map (fun ss -> new_block "switch.default", ss) dfl
        and endb   = new_block "switch.end" in
        let st'    =
          match st with
          | InswitchInloop (post, _)
            | Inloop (post, _) -> InswitchInloop (post, endb)
          | _                  -> Inswitch endb
        in
        let nextb  =
          match dflb with
          | Some (b, _) -> b
          | None        -> endb in
        codegen_stmt_cases lv st' ce (get_typ e) (List.combine blocks cs) nextb endb;
        Option.iter (fun (b, ss) ->
            position_at_end b g.builder;
            let tm = codegen_stmt_list lv st' ss in
            if not tm then
              ignore (build_br endb g.builder)
          ) dflb;

        position_at_end bb g.builder;
        begin match blocks, dflb with
        | [], Some (b, _)
          | b :: _, _ -> ignore (build_br b g.builder)
        | [], None    -> ignore (build_br endb g.builder)
        end;

        position_at_end endb g.builder;
        false

     | For (_, b, e, p, ss)      ->
        codegen_simp_stmt lv b;
        let func = current_func () in
        let bb   = current_block () in

        let predb  = new_block "for.predicate" in
        jump_to_this bb;
        let pred   =
          match e with
          | None -> true_val
          | Some e -> codegen_expr lv e
        in
        let predb' = current_block () in

        let body = new_block "for.body" in
        let post = new_block "for.post" in
        let endb = new_block "for.end" in

        position_at_end body g.builder;
        let tm = codegen_stmts lv (Inloop (post, endb)) ss in
        if not tm then
          ignore (build_br post g.builder);

        position_at_end post g.builder;
        codegen_simp_stmt lv p;
        ignore (build_br predb g.builder);

        position_at_end endb g.builder;
        cond_branch pred predb' body endb;
        false
     | Continue m                ->
        begin match st with
        | InswitchInloop (post, _)
          | Inloop (post, _) ->
           ignore (build_br post g.builder);
        | _                  -> raise (TcInconsistency (m, "continue can not be place out side of the loop"))
        end;
        true
     | Break m                   ->
        begin match st with
        | InswitchInloop (_, b)
          | Inloop (_, b)
          | Inswitch b ->
           ignore (build_br b g.builder)
        | _            -> raise (TcInconsistency (m, "continue can not be place out side of the loop"))
        end;
        true           

  and codegen_stmt_list lv st (ss : stmt list) : bool =
    (* codegen until the first return. LLVM require each bb has precisely one exit point.
     *)
    List.exists (codegen_stmt lv st) ss

  and codegen_stmts lv st (ss : stmts) : bool =
    codegen_stmt_list lv st ss.data

  and codegen_stmt_case_pred lv ce t es next =
    let bb  = current_block () in
    let exb = new_block "switch.case.exec" in

    let rec iter es =
      match es with
      | []      -> ()
      | [e]     ->
         let ce' = codegen_expr lv e in
         let cmp = codegen_expr_eq (expr_meta e) t ce ce' in
         cond_branch cmp (current_block ()) exb next
      | e :: es ->
         let ce' = codegen_expr lv e in
         let cmp = codegen_expr_eq (expr_meta e) t ce ce' in
         let cb  = current_block () in
         let nb  = new_block "switch.case.pred" in
         cond_branch cmp cb exb nb;
         iter es
    in
    position_at_end bb g.builder;
    iter es;
    exb

  and codegen_stmt_case lv st ce t b case next endb =
    position_at_end b g.builder;
    let exb = codegen_stmt_case_pred lv ce t case.cond next in
    position_at_end exb g.builder;
    let tm  = codegen_stmt_list lv st case.exec in
    if not tm then
      ignore (build_br endb g.builder)

  and codegen_stmt_cases lv st ce t cases next endb =
    match cases with
    | []                              -> ()
    | [b, c]                          -> codegen_stmt_case lv st ce t b c next endb
    | (cb, c) :: ((b, _) as c2) :: cs ->
       codegen_stmt_case lv st ce t cb c b endb;
       codegen_stmt_cases lv st ce t (c2 :: cs) next endb

  and codegen_stmt_print_helper lv es =
    let f e =
      let ce = codegen_expr lv e in
      if rt_expr e === Tbool then
        build_select ce
                     (get_str_lit "true")
                     (get_str_lit "false")
                     "" g.builder
      else ce
    in
    let fmt e =
      match rt_expr e with
      | Tstr   -> "%s"
      | Tint   -> "%d"
      | Tfloat -> "%+le"
      | Trune  -> "%d"
      | Tbool  -> "%s"
      | _      -> raise (TcInconsistency (expr_meta e, "the expression has no print format"))
    in 
    let ces = List.map f es in
    let fmt = List.map fmt es in
    fmt, ces

end
