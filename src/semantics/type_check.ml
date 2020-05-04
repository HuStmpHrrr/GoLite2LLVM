open Env
open Env_helper
open Syntax
open Conversion
open Utils
open Meta
open Typed

(* binding related *)
exception InvalidBlankLocation of unit meta
exception VariableNotFound     of string meta
exception DuplicateField       of Untyped.typ * string meta * string meta

(** the first argument is used as an expression but is a type defined as the third
   argument in second argument *)
exception KindMismatch1        of string meta * string meta * typ

(** the first argument is used as a type but requires a variable in the second
   argument having the third argument as type to be resolved as a type *)
exception KindMismatch2        of string meta * string meta * typ

exception AssignToConst        of string meta * string meta * typ

(* type resolution related *)
exception TypeNotDefined       of string meta

exception InvalidRecursiveType of string meta * Untyped.typ

(* general type checking error *)
(** expr is expected to have types in the list *)
exception TypeMismatch         of expr * typ list

(** epxr is expected to have types _resolved_ to the types in the list *)
exception ResolvedTypeMismatch of expr * typ list

exception NotComparable        of expr

(** a index operation fails to find a field in the type *)
exception FieldNotFound        of expr * string
exception ExpectArrOrSlice     of expr
exception ExpectSlice          of expr
exception InvalidLHS           of Untyped.expr

(* function related *)
exception ExpectFunc           of expr
exception ParamTooFew          of Untyped.expr * typ list
exception ParamTooMany         of Untyped.expr * typ list
                        
(* type cast related *)
(** the string is the name of the Tref (string because it could be a defined type) *)
exception CastParamMustOne     of Untyped.expr * string

(** failed to perform type cast from typ of expr to string *)
exception CastError            of string * expr

(* statement related *)
exception VDeclNumMismatch     of name meta list * Untyped.expr list
exception MissingType          of unit meta
exception NumOfSidesMismatch   of Untyped.expr list * Untyped.expr list
exception RedeclInShortDecl    of string meta * string meta
exception NewVarInShortDecl    of unit meta * name meta list
exception UnassignableType     of expr
exception AssignOpTypeMismatch of (unit meta * typ * typ)

exception SpecialFuncWrongType of string meta

 (* return type *)
exception ReturnTypeMismatch   of unit meta * typ * typ
exception MissingTermStmt      of name meta * typ

let cast_to t1 t2 =
  is_base t1 && is_base t2 &&
    (t1 === t2
     || is_numeric t1 && is_numeric t2
     || t1 === Tstr && is_integer t2)

let check_fields_dup t fs =
  let open Utils in
  let rec iter fs acc =
    match fs with
    | []           -> ()
    | (n, _) :: fs ->
       match n.data with
       | Blank -> iter fs acc
       | X x   ->
          match SMap.add acc ~key:x ~data:n with
          | `Ok m      -> iter fs m
          | `Duplicate ->
             let existed = SMap.find_exn acc x in
             raise (DuplicateField (t, update_data existed x, update_data n x)) in
  iter fs SMap.empty

let sanitize_fields m fs f =
  let t = Untyped.Tstruct (m, fs) in
  let fs = Core.List.bind fs ~f:(fun (ns, t) -> let t' = f t in List.map (fun n -> (n, t')) ns) in
  check_fields_dup t fs;
  List.map (fun (n, t) -> n.data, t) fs

(** finds the actual type representations of the syntactical types *)
let rec tc_typ (g : env) (t : Untyped.typ) : typ =
  match t with
  | Untyped.Tref n              ->
     begin match find_opt n.data g with
     | None                    -> raise (TypeNotDefined n)
     | Some (BConst _, m)      ->
        raise (KindMismatch2 (n, update_data m n.data, Tbool))
     | Some (Func t, m)
       | Some (Gbnd t, m)
       | Some (Lbnd (_, t), m) ->
        raise (KindMismatch2 (n, update_data m n.data, t))
     | Some (Tbnd t, m)        ->
        Tref (update_data m n.data, resolved_typ_l t)
     | Some (Alias t, m)       -> t
     end
  | Untyped.Tslice (_, t)       -> Tslice (tc_typ g t)
  | Untyped.Tarray (_, k, i, t) -> Tarray (to_int32 k i, tc_typ g t)
  | Untyped.Tstruct (m, fs)     ->
     Tstruct (sanitize_fields m fs (tc_typ g))

(** type check an expression on the right hand side *)
let rec tc_expr_r (g : env) (e : Untyped.expr) : expr =
  match e with
  | Untyped.Var x               ->
     begin match x.data with
     | Blank -> raise (InvalidBlankLocation (forget_data x))
     | X x'  ->
        match find_opt x' g with
        | None                         -> raise (VariableNotFound (update_data x x'))
        | Some (Func t, m)
          | Some (Gbnd t, m)           -> GVar (update_data x x', t)
        | Some (Lbnd (i, t), m)        -> LVar (update_data x x', i, t)
        | Some (BConst b, m)           -> Bool (update_data x b)
        | Some ((Tbnd t | Alias t), m) -> raise (KindMismatch1 (update_data x x', update_data m x', t))
     end
   | Untyped.Int (k, i)         -> Int (k, i)
   | Untyped.Float (k, f)       -> Float (k, f)
   | Untyped.Bool b             -> Bool b
   | Untyped.Rune (s, c)        -> Rune (s, c)
   | Untyped.String (k, s, sm)  -> String (k, s, sm)
   | Untyped.App (m, f, es)     -> tc_app_r g m f es
   | Untyped.Append (m, e1, e2) -> tc_append g m e1 e2
   | Untyped.Cap (m, e)         -> tc_cap g m e
   | Untyped.Len (m, e)         -> tc_len g m e
   | Untyped.Sel (m, e, s)      ->
      let ee = tc_expr_r g e in
      let te = get_typ ee in
      begin match resolved_typ te with
      | Tstruct fs ->
         begin match find_field s fs with
         | None        -> raise (FieldNotFound (ee, s))
         | Some (i, t) -> Sel (m, ee, i, s, t)
         end
      | _          -> raise (FieldNotFound (ee, s))
      end
   | Untyped.Idx (m, e1, e2)    ->
      let ee1 = tc_expr_r g e1 in
      begin match resolved_typ (get_typ ee1) with
      | Tarray (_, t)
        | Tslice t ->
         let ee2 = tc_expr_r g e2 in
         if rt_expr ee2 === Tint then Idx (m, ee1, ee2, t)
         else raise (ResolvedTypeMismatch (ee2, [Tint]))
      | _          -> raise (ExpectArrOrSlice ee1)
      end
   | Untyped.Binop (op, e1, e2) ->
      let ee1 = tc_expr_r g e1
      and ee2 = tc_expr_r g e2 in
      tc_combine_binop op ee1 ee2
   | Untyped.Uniop (op, e)      ->
      let ee = tc_expr_r g e in
      let te = get_typ ee in
      begin match op.data with
      | Pos | Neg ->
         if resolve_to_numeric ee
         then Uniop (op, ee, te)
         else raise (ResolvedTypeMismatch (ee, numerics))
      | Not ->
         if rt_expr ee === Tbool
         then Uniop (op, ee, te)
         else raise (ResolvedTypeMismatch (ee, [Tbool]))
      | Bcomp ->
         if resolve_to_integer ee
         then Uniop (op, ee, te)
         else raise (ResolvedTypeMismatch (ee, integers))
      end
   | Untyped.Paren e            -> tc_expr_r g e

and tc_append g m e1 e2 =
  let ee1 = tc_expr_r g e1
  and ee2 = tc_expr_r g e2 in
  let te1 = rt_expr ee1 in
  match te1 with
  | Tslice t ->
     if t === get_typ ee2 then
       Append (m, ee1, ee2)
     else raise (TypeMismatch (ee2, [t]))
  | _        -> raise (ExpectSlice ee1)

and tc_cap g m e =
  let ee = tc_expr_r g e in
  let te = rt_expr ee in
  match te with
  | Tslice _ | Tarray (_, _) -> (* we could have replaced the int here, but whatever *)
     Cap (m, ee)
  | _                        -> raise (ExpectArrOrSlice ee)

and tc_len g m e =
  let ee = tc_expr_r g e in
  let te = rt_expr ee in
  match te with
  | Tstr
    | Tslice _
    | Tarray (_, _) ->
     Len (m, ee)
  | _               -> raise (ExpectArrOrSlice ee)

and tc_app_r g m f es =
  let wrap () =
    let (m, fe, es, r) = tc_app_func_r g m f es in
    App (m, fe, es, r) in
  match f with
  | Untyped.Var ({data = X x'} as x) ->
     begin match find_opt x' g with
     | None                  -> raise (VariableNotFound (update_data x x'))
     | Some ((Tbnd _
              | Alias _), m) ->
        (* here this application is in fact a type cast *)
        let t' = tc_typ g (Untyped.Tref (update_data x x')) in
        let t  = resolved_typ t' in
        begin match es with
        | [ e ] ->
           let ee = tc_expr_r g e in
           if cast_to t (rt_expr ee) then
             Cast (m, update_data x x', ee, t')
           else raise (CastError (x', ee))
        | _     -> raise (CastParamMustOne (Untyped.App (m, f, es), x'))
        end
     | Some _                -> wrap ()
     end
  | _ -> wrap ()

and tc_app_func_r g m f es =
    let fe = tc_expr_r g f in
    match get_typ fe with
    | Tfun (ts, r) -> 
       let rec iter_tc es' ts' =
         match es', ts' with
         | []      , []       -> []
         | e :: es , t :: ts' ->
            let te = tc_expr_r g e in
            if get_typ te === t then te :: iter_tc es ts'
            else raise (TypeMismatch (te, [t]))
         | e :: es , []       -> raise (ParamTooMany (e, ts))
         | []      , t :: ts  -> raise (ParamTooFew (Untyped.App (m, f, es), t :: ts))
       in
       (m, fe, iter_tc es ts, r)
    | tf           -> raise (ExpectFunc fe)

and tc_combine_binop op ee1 ee2 = 
  let te1 = get_typ ee1
  and te2 = get_typ ee2 in
  if te1 <!> te2 then raise (TypeMismatch (ee2, [te1]))
  else 
    begin match op.data with
    | Lo Or | Lo And -> 
       if rt_expr ee1 === Tbool
       then Binop (op, ee1, ee2, te1)
       else raise (ResolvedTypeMismatch (ee1, [Tbool]))
    | Lo Eq | Lo Neq ->
       if resolve_to_comparable ee1
       then Binop (op, ee1, ee2, Tbool)
       else raise (NotComparable ee1)
    | Lo Le | Lo Lt | Lo Ge | Lo Gt ->
       if resolve_to_ordered ee1
       then Binop (op, ee1, ee2, Tbool)
       else raise (ResolvedTypeMismatch (ee1, ordereds))
    | Ar Plus ->
       let rt = rt_expr ee1 in
       if is_numeric rt || rt === Tstr
       then Binop (op, ee1, ee2, te1)
       else raise (ResolvedTypeMismatch (ee1, Tstr :: numerics))
    | Ar Minus | Ar Times | Ar Div ->
       if resolve_to_numeric ee1
       then Binop (op, ee1, ee2, te1)
       else raise (ResolvedTypeMismatch (ee1, numerics))
    | Ar Rem | Ar Bor | Ar Band | Ar Bxor
      | Ar Bclear | Ar Lshift | Ar Rshift ->
       if resolve_to_integer ee1
       then Binop (op, ee1, ee2, te1)
       else raise (ResolvedTypeMismatch (ee1, integers))
    end

let tc_expr_assn g e =
  let ee = tc_expr_r g e in
  if is_assignable (get_typ ee) then ee
  else raise (UnassignableType ee)

let rec tc_aexpr (g : env) (e : Untyped.expr) : aexpr =
  match e with
  | Untyped.Var x ->
    begin match x.data with
    | Blank -> raise (InvalidBlankLocation (forget_data x))
    | X x'  -> (* tc var a typ *)
      match find_opt x' g with 
      | None                         -> raise (VariableNotFound (update_data x x')) (* trying to redefine a =  *)
      | Some (Gbnd t, m)             -> AGVar (update_data x x', t)
      | Some (Lbnd (i, t), m)        -> ALVar (update_data x x', i, t)
      | Some ((Tbnd t | Alias t), m) -> raise (KindMismatch2 (update_data x x', update_data m x', t))
      | Some (BConst _, m)           -> raise (AssignToConst (update_data x x', update_data m x', Tbool))
      | Some (Func t, m)             -> raise (AssignToConst (update_data x x', update_data m x', t))
    end
  | Untyped.Sel (m, e, s) -> (* tc p.x *)
      let ee = tc_aexpr g e in
      let te = get_atyp ee in
      begin match resolved_typ te with
      | Tstruct fs ->
         begin match find_field s fs with
         | None        -> raise (FieldNotFound (aexpr_to_expr ee, s))
         | Some (i, t) -> ASel (m, ee, i, s, t)
         end
      | _          -> raise (FieldNotFound (aexpr_to_expr ee, s))
      end
  | Untyped.Idx (m, e1, e2)    ->
      let ee1 = tc_aexpr g e1 in
      begin match resolved_typ (get_atyp ee1) with
      | Tarray (_, t)
        | Tslice t ->
         let ee2 = tc_expr_r g e2 in
         if rt_expr ee2 === Tint then AIdx (m, ee1, ee2, t)
         else raise (ResolvedTypeMismatch (ee2, [Tint]))
      | _          -> raise (ExpectArrOrSlice (aexpr_to_expr ee1))
      end
  | _ -> raise (InvalidLHS e)


(** type check an expression on the left hand side *)
let tc_expr_l (g : env) (e : Untyped.expr) : lexpr =
  match e with
  | Untyped.Var ({data = Blank} as x) -> LBlank (forget_data x)
  | _ -> LAexpr (tc_aexpr g e)

(** this function is distinct from [tc_typ].
    
    we need two distinct functions for two different usages:
    1. [tc_typ_d] is responsible for converting an untyped typ to a semantic
       typ in a type definition.
    2. [tc_typ] is reponsible for converting an untyped typ to a semantic
       typ anywhere else.

    the reason for this distinction is that in a type definition permits 
    recursive references. therefore, from a judgmental form of view, the type 
    checking must do additional treatment in order to ensure a proper self-referencing
    semantic typ is eventually produced.
 *)
let tc_typ_d (g : env) (x : string meta) (lt : unit -> typ) (t : Untyped.typ) : typ =
  let rec iter t' =
  match t' with
  | Untyped.Tref n               ->
     if x.data = n.data then Tref (x, Lazy.from_fun lt)
     else
       begin match find_opt n.data g with
       | None               -> raise (TypeNotDefined n)
       | Some (Func t, m)
         | Some (Lbnd (_, t), m)
         | Some (Gbnd t, m) ->
          raise (KindMismatch2 (n, update_data m n.data, t))
       | Some (BConst _, m) ->
          raise (KindMismatch2 (n, update_data m n.data, Tbool))
       | Some (Tbnd t, m)   ->
          Tref (update_data m n.data, Lazy.from_val (resolved_typ t))
       | Some (Alias t, m)  -> t
       end
  | Untyped.Tslice (_, t')       -> Tslice (iter t')
  | Untyped.Tarray (_, k, i, t') -> Tarray (to_int32 k i, conv t')
  | Untyped.Tstruct (m, fs)      -> Tstruct (sanitize_fields m fs conv)
  and conv t' =
    match t' with
    | Untyped.Tref n
         when x.data = n.data -> raise (InvalidRecursiveType (n, t))
    | _                       -> iter t' in
  conv t

let rec tc_decl : 'a. 'a decl_env -> Untyped.decl -> 'a decl_env * 'a decl list =
  fun g d -> 
  match d with
  | Untyped.VarDecl (m, ns, t, es) ->
     let (g', d) = tc_var_decl g m ns t es in
     g', [d]
  | Untyped.VarDecls ds            ->
     Core.List.fold_map ds.data ~init:g
                        ~f:(fun g (m, ns, t, es) -> tc_var_decl g m ns t es)
  | Untyped.TypDecl (m, n, t)      ->
     tc_typ_decl g m n t
  | Untyped.TypDecls ds            ->
     acc_map (fun g (m, n, t) -> tc_typ_decl g m n t) g ds.data

and tc_var_decl :
      'a. 'a decl_env -> unit meta -> name meta list -> Untyped.typ option -> Untyped.expr list ->
      'a decl_env * 'a decl =
  fun g m ns t es ->
  match es with
  | [] ->
     begin match t with
     | Some t ->
        let ug  = underl_env g in
        let t'  = tc_typ ug t in
        let ng, ns'  = add_names_bnds g (List.map (fun n -> n, t') ns) in
        ng, VarDecl2 (m, ns', t')
     | None   -> raise (MissingType m)
     end
  | _  ->
     if List.length ns <> List.length es then raise (VDeclNumMismatch (ns, es))
     else
       let ug  = underl_env g in
       let ees = List.map (tc_expr_assn ug) es in
       let nes = List.combine ns ees in
       match t with
       | Some t ->
          let t'  = tc_typ ug t in
          let nt' = List.map (fun (n, e) -> if get_typ e <!> t' then raise (TypeMismatch (e, [t']))
                                            else n, t') nes in
          let ng, ns' = add_names_bnds g nt' in
          ng, VarDecl3 (m, List.combine ns' ees, t')
       | None ->
          let nt' = List.map (fun (n, e) -> n, get_typ e) nes in
          let ng, ns' = add_names_bnds g nt' in
          ng, VarDecl1 (m, List.combine ns' ees)

and tc_typ_decl :
      'a. 'a decl_env -> unit meta -> name meta -> Untyped.typ -> 'a decl_env * 'a decl list =
  fun g m n t ->
  match n.data with
  | Blank ->                    (* in this very special case, there is no recursion going on *)
     let _ = tc_typ (underl_env g) t in g, []
  | X x   ->
     let ug = underl_env g in
     let tf =
       let r = ref None in
       let rec f = fun () ->
         match !r with
         | None ->
            let t' = tc_typ_d ug (update_data n x) (fun () -> resolved_typ (f ())) t in
            r := Some t';
            t'
         | Some t' -> t'
       in
       f in
     let t' = tf () in
     let rt = resolved_typ t' in
     let x' = update_data n x in
     match add_opt x' (Tbnd t') ug with
     | New g'          -> update_underl_env g g', [TypDecl (m, x', t')]
     | Found (n, k, m) -> raise (Redecl (n, k, m))

let tc_simp_stmt (g : exenv) (s : Untyped.simp_stmt) : exenv * simp_stmt =
  match s with
   | Untyped.Nop m                    -> g, Nop m
   | Untyped.FApp (m, f, es)          ->
      let (m, fe, es, r) = tc_app_func_r g.underl m f es in
      g, FApp (m, fe, es, r)
   | Untyped.Incr e                   ->
      let ae = tc_aexpr g.underl e.data in
      let te = resolved_typ (get_atyp ae) in
      if is_integer te || te === Tfloat then g, Incr (update_data e ae)
      else raise (ResolvedTypeMismatch (aexpr_to_expr ae, Tfloat :: integers))
   | Untyped.Decr e                   ->
      let ae = tc_aexpr g.underl e.data in
      let te = resolved_typ (get_atyp ae) in
      if is_integer te || te === Tfloat then g, Decr (update_data e ae)
      else raise (ResolvedTypeMismatch (aexpr_to_expr ae, Tfloat :: integers))
   | Untyped.Assign (m, es1, es2)     ->
      if List.length es1 <> List.length es2 then raise (NumOfSidesMismatch (es1, es2))
      else
        let les = List.map (tc_expr_l g.underl) es1
        and ees = List.map (tc_expr_r g.underl) es2 in
        let res = List.combine les ees in
        List.iter (fun (le, ee) ->
            match get_ltyp le with
            | Any -> ()
            | T t -> if t === get_typ ee then ()
                     else raise (TypeMismatch (ee, [t]))) res;
        g, Assign (m, res)
   | Untyped.AssignOp (m, e1, op, e2) ->
      let ae   = tc_aexpr g.underl e1
      and ee   = tc_expr_r g.underl e2 in
      let comp = tc_combine_binop (update_data m (Ar op)) (aexpr_to_expr ae) ee in
      if get_typ comp <!> get_atyp ae then raise (AssignOpTypeMismatch (m, get_atyp ae, get_typ comp))
      else g, AssignOp (m, ae, op, ee)
   | Untyped.ShortDecl (m, ns, es)    ->
      let tc_pair g n e =
        match n.data with
        | Blank -> g, (update_data n SBlank, e)
        | X x   ->
           let t = get_typ e in
           match add_name_bnd_s (Local g) n t with
           | `Ok (g', ni)                      -> from_local g', (update_data ni (new_lname ni.data), e)
           | `Found (_, Lbnd (i, t'), m)       ->
              if t <!> t' then raise (TypeMismatch (e, [t']))
              else g, (update_data n (Existed i), e)
           | `Found (_, Gbnd t, m)             ->
              raise Impossible  (* it is impossible because we must have higher frames when type checking simp_stmt *)
           | `Found (_, (Tbnd t | Alias t), m) ->
              raise (KindMismatch1 (update_data n x, update_data m x, t))
           | `Found (_, Func t, m)             ->
              raise (AssignToConst (update_data n x, update_data m x, t))
           | `Found (_, BConst _, m)           ->
              raise (AssignToConst (update_data n x, update_data m x, Tbool)) in
      let rec check_dup ns acc =
        match ns with
        | []      -> ()
        | n :: ns ->
           match n.data with
           | Blank -> check_dup ns acc
           | X x   ->
              match SMap.add acc ~key:x ~data:n with
              | `Ok acc    -> check_dup ns acc
              | `Duplicate ->
                 let n' = SMap.find_exn acc x in
                 raise (RedeclInShortDecl (update_data n x, update_data n' x)) in
      if List.length ns <> List.length es then raise (VDeclNumMismatch (ns, es))
      else
        begin
          check_dup ns SMap.empty;
          let g', nes = Core.List.fold_map (List.combine ns (List.map (tc_expr_assn g.underl) es))
                                           ~init:g
                                           ~f:(fun g (n, e) -> tc_pair g n e) in
          if List.exists (fun (n, _) -> is_new n.data) nes
          then g', ShortDecl (m, nes)
          else raise (NewVarInShortDecl (m, ns))
        end

let rec tc_stmt (r : typ) (g : exenv) (s : Untyped.stmt) : exenv * stmt list =
  match s with
  | Untyped.Simpl s                   ->
     let g', s' = tc_simp_stmt g s in
     g', [Simpl s']
  | Untyped.Decl d                    ->
     let g', ds = tc_decl (Local g) d in
     from_local g', List.map (fun d -> Decl d) ds
  | Untyped.Block ss                  ->
     let g', ss' = tc_stmts r (exenv_new_frame g) ss in
     update_locals g g', [Block ss']
  | Untyped.Print es                  -> g, [Print (update_data es (tc_prints g es.data))]
  | Untyped.Println es                -> g, [Println (update_data es (tc_prints g es.data))]
  | Untyped.Return e                  ->
     begin match e.data with
     | None    -> if r === Tvoid then g, [Return (update_data e None)]
                  else raise (ReturnTypeMismatch (forget_data e, r, Tvoid))
     | Some e' ->
        let e' = tc_expr_assn g.underl e' in
        let t' = get_typ e' in
        if r === t' then g, [Return (update_data e (Some e'))]
        else raise (ReturnTypeMismatch (forget_data e, r, t'))
     end
  | Untyped.If (m, s, e, ifs, els)    ->
     let g', ts = tc_simp_stmt (exenv_new_frame g) s in
     let ee     = tc_expr_r g'.underl e in
     let nfg    = exenv_new_frame g' in
     if rt_expr ee <!> Tbool then raise (ResolvedTypeMismatch (ee, [Tbool]))
     else
       let ifg, ifs' = tc_stmts r nfg ifs in
       begin match els with
       | None    -> update_locals g ifg, [If (m, ts, ee, ifs', None)]
       | Some ss ->
          let elg, els' = tc_stmts r (update_locals nfg ifg) ss in
          update_locals g elg, [If (m, ts, ee, ifs', Some els')]
       end
  | Untyped.Switch (m, s, e, cs, dfl) ->
     let g', ts = tc_simp_stmt (exenv_new_frame g) s in
     let ee     = tc_expr_r g'.underl e in
     let nfg    = exenv_new_frame g' in
     if not (resolve_to_comparable ee) then raise (NotComparable ee)
     else
       let csg, cs' = Core.List.fold_map cs ~init:nfg ~f:(tc_case r (get_typ ee)) in
       begin match dfl with
       | None    ->
          update_locals g csg, [Switch (m, ts, ee, cs', None)]
       | Some ss ->
          let dfg, dfl' = tc_stmt_list r (update_locals nfg csg) ss in
          update_locals g dfg, [Switch (m, ts, ee, cs', Some dfl')]
       end
  | Untyped.For (m, s1, e, s2, ss)    ->
     let g', ts1 = tc_simp_stmt (exenv_new_frame g) s1 in
     let ee      = Option.map (tc_expr_r g'.underl) e in
     let _, ts2  = tc_simp_stmt g' s2 in
     let nfg     = exenv_new_frame g' in
     begin match ee with
     | Some e
          when rt_expr e <!> Tbool -> raise (ResolvedTypeMismatch (e, [Tbool]))
     | _                           -> 
       let ssg, ss' = tc_stmts r nfg ss in
       update_locals g ssg, [For (m, ts1, ee, ts2, ss')]
     end
  | Untyped.Break m                   -> g, [Break m]
  | Untyped.Continue m                -> g, [Continue m]

and tc_prints g es =
  let ees = List.map (tc_expr_r g.underl) es in
  List.iter (fun e -> if not (is_base (rt_expr e)) then raise (ResolvedTypeMismatch (e, bases))) ees;
  ees

and tc_case r t g (c : Untyped.case) : exenv * case =
  let ees = List.map (tc_expr_r g.underl) c.cond in
  List.iter (fun ee -> if get_typ ee <!> t then raise (TypeMismatch (ee, [t]))) ees;
  let g', tss = tc_stmt_list r g c.exec in
  update_locals g g', {
    cond = ees;
    exec = tss;
  }
  
and tc_stmt_list r (g : exenv) (ss : Untyped.stmt list) : exenv * stmt list =
  acc_map (tc_stmt r) g ss
and tc_stmts r (g : exenv) (ss : Untyped.stmts) : exenv * stmts =
  let g', ss' = tc_stmt_list r g ss.data in
  g', update_data ss ss'

let check_special_names (d : gdecl) =
  let check n =
    match n.data with
    | "main" | "init" ->
       raise (SpecialFuncWrongType n)
    | _               -> () in
  let check_name n =
    match n.data with
    | Blank -> ()
    | X x   -> check (update_data n x) in
  match d with
  | VarDecl1 (_, bs)    -> List.iter (fun (n, _) -> check_name n) bs
  | VarDecl2 (_, ns, _) -> List.iter check_name ns
  | VarDecl3 (_, bs, _) -> List.iter (fun (n, _) -> check_name n) bs
  | TypDecl (_, n, _)   -> check n
  
let tc_top_decl (g : env) (d : Untyped.top_decl) : env * top_decl list =
  match d with
  | Untyped.DDecl d ->
     let g', ds = tc_decl (Global g) d in
     List.iter check_special_names ds;
     underl_env g', List.map (fun d -> DDecl d) ds
  | Untyped.FunDecl (m, f, bs, t, ss) ->
     match f.data with
     | X "init" ->
        let ns' = Core.List.bind bs ~f:(fun (ns, t) -> let t' = tc_typ g t in List.map (fun n -> n, t') ns) in
        let t'  = match t with | None -> Tvoid | Some t -> tc_typ g t in
        let ft  = Tfun (List.map snd ns', t') in
        if ft <!> Tfun ([], Tvoid) then raise (SpecialFuncWrongType (update_data f "init"))
        else
          let dg, lns  = add_names_bnds (Local (extend (new_frame g))) ns' in
          let eg       = from_local dg in
          let eg', ss' = tc_stmts Tvoid eg ss in
          g, [FunDecl (m, f, List.combine lns (List.map snd ns'), t', List.rev eg'.locals, ss')]
     | _        ->
        (* we first insert the type to the environment (bg for bogus) temporarily when we call tc_typ *)
        let bg  = add_name_kind g f (Func Tvoid) in
        let ns' = Core.List.bind bs ~f:(fun (ns, t) -> let t' = tc_typ bg t in List.map (fun n -> n, t') ns) in
        let t'  = match t with | None -> Tvoid | Some t -> tc_typ bg t in 
        let ft  = Tfun (List.map snd ns', t') in
        if f.data = X "main" && ft <!> Tfun ([], Tvoid) then raise (SpecialFuncWrongType (update_data f "main"))
        else
          let g'       = add_name_kind g f (Func ft) in
          let dg, lns  = add_names_bnds (Local (extend (new_frame g'))) ns' in
          let eg       = from_local dg in
          let eg', ss' = tc_stmts t' eg ss in
          g', [FunDecl (m, f, List.combine lns (List.map snd ns'), t', List.rev eg'.locals, ss')]

(** https://golang.org/ref/spec#Terminating_statements *)
let check_return ds =
  let rec has_break_stmt (s : stmt) : bool =
    match s with
     | Block ss             -> has_break_stmt_list ss.data
     | If (_, _, _, tr, fl) ->
        has_break_stmt_list tr.data && Core.Option.exists fl ~f:(fun ss -> has_break_stmt_list ss.data)
     | Break _              -> true
     | _                    -> false
  and has_break_stmt_list (s : stmt list) : bool =
    List.exists has_break_stmt s
  in

  let rec check_stmt (s : stmt) : bool =
    match s with
     | Return _                      -> true
     | Block ss                      -> check_stmts ss
     | If (_, _, _, tr, Some fl)     -> check_stmts tr && check_stmts fl
     | Switch (_, _, _, cs, Some ss) ->
        List.for_all (fun ss -> check_stmt_list ss && not (has_break_stmt_list ss)) (ss :: List.map (fun c -> c.exec) cs)
     | For (_, _, None, _, ss)       -> not (has_break_stmt_list ss.data)
     | _                             -> false
  and check_stmt_list (ss : stmt list) : bool =
    match init_last ss with
    | None         -> false
    | Some (s, ss) -> check_stmt s
  and check_stmts ss : bool = check_stmt_list ss.data
  in

  let check_func d =
    match d with
    | FunDecl (_, f, _, r, _, ss) ->
       if r === Tvoid then ()
       else if check_stmts ss then ()
       else raise (MissingTermStmt (f, r))
    | _ -> ()
  in List.iter check_func ds


let tc_program_gen (g : env) (p : Untyped.program) : env * program =
  let g', ds = acc_map tc_top_decl g p.top_decls in
  check_return ds;
  g' , {
      pkg_decl  = p.pkg_decl;
      top_decls = ds
    }


let tc_program = tc_program_gen default_env
