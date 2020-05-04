open Meta
open Tags
open Common

(* Special notes:

1. we do not need a case for so-called "casting", because it's just normal 
   type conversion function, which got created when a type is declared.
 *)


type expr =
  | Var    of name meta
  | Int    of int_kind * string meta
  | Float  of float_kind * string meta
  | Bool   of bol meta
  | Rune   of string * char meta
  | String of str_kind * string * string meta
  (** e0(e1, e2, ... , en)  *)
  | App    of unit meta * expr * expr list
  | Append of unit meta * expr * expr
  | Len    of unit meta * expr
  | Cap    of unit meta * expr
  | Sel    of unit meta * expr * string
  (** e1[ e2 ] *)
  | Idx    of unit meta * expr * expr
  | Binop  of binop meta * expr * expr
  | Uniop  of uniop meta * expr
  | Paren  of expr

let rec expr_meta e =
  match e with
  | Var x            -> forget_data x
  | Int (_, i)       -> forget_data i
  | Float (_, f)     -> forget_data f
  | Bool b           -> forget_data b
  | Rune (_, c)      -> forget_data c
  | String (_, _, s) -> forget_data s
  | App (m, _, _)    -> m
  | Append (m, _, _) -> m
  | Cap (m, _)       -> m
  | Len (m, _)       -> m
  | Sel (m, _, _)    -> m
  | Idx (m, _, _)    -> m
  | Binop (m, _, _)  -> forget_data m
  | Uniop (m, _)     -> forget_data m
  | Paren e          -> expr_meta e

let is_true e =
  match e with
  | Bool b -> b.data = True
  | _      -> false
                     
type typ =
  (* | Tstr | Tint | Tfloat | Trune | Tbool *)
  | Tref    of string meta
  | Tslice  of unit meta * typ
  | Tarray  of unit meta * int_kind * string meta * typ
  | Tstruct of unit meta * (name meta list * typ) list

let typ_meta (t : typ) =
  match t with
  | Tref t              -> forget_data t
  | Tslice (m, _)       -> m
  | Tarray (m, _, _, _) -> m
  | Tstruct (m, _)      -> m

type simp_stmt =
  | Nop       of unit meta
  | FApp      of unit meta * expr * expr list
  | Incr      of expr meta
  | Decr      of expr meta
  | Assign    of unit meta * expr list * expr list
  | AssignOp  of unit meta * expr * arith * expr
  | ShortDecl of unit meta * name meta list * expr list

let simp_stmt_meta s =
  match s with
  | Nop m                 -> m
  | FApp (m, _, _)        -> m
  | Incr e                -> forget_data e
  | Decr e                -> forget_data e
  | Assign (m, _, _)      -> m
  | AssignOp (m, _, _, _) -> m
  | ShortDecl (m, _, _)   -> m

let is_nop s =
  match s with
  | Nop _ -> true
  | _     -> false

type decl =
  | VarDecl  of unit meta * name meta list * typ option * expr list
  (** list of variable declarations in a single parsing unit.
   * 
   * each entry in a list represents a list of variables, an optional type and a list of expression.
   *)
  | VarDecls of (unit meta * name meta list * typ option * expr list) list meta
  | TypDecl  of unit meta * name meta * typ
  | TypDecls of (unit meta * name meta * typ) list meta

let decl_meta d = 
  match d with
  | VarDecl (m, _, _, _) -> m
  | VarDecls v           -> forget_data v
  | TypDecl (m, _, _)    -> m
  | TypDecls t           -> forget_data t
              
type case = {
    cond : expr list;
    exec : stmt list
  }
and stmt =
  | Simpl    of simp_stmt
  | Decl     of decl
  | Block    of stmts
  | Print    of expr list meta
  | Println  of expr list meta
  | Return   of expr option meta
  | If       of unit meta * simp_stmt * expr * stmts * stmts option
  | Switch   of unit meta * simp_stmt * expr * case list * stmt list option
  | For      of unit meta * simp_stmt * expr option * simp_stmt * stmts
  | Break    of unit meta
  | Continue of unit meta
and stmts = stmt list meta

let stmts_meta (ss : stmts) = forget_data ss

let stmt_meta s =
  match s with
  | Simpl s                -> simp_stmt_meta s
  | Decl d                 -> decl_meta d
  | Block ss               -> stmts_meta ss
  | Print p                -> forget_data p
  | Println p              -> forget_data p
  | Return r               -> forget_data r
  | If (m, _, _, _, _)     -> m
  | Switch (m, _, _, _, _) -> m
  | For (m, _, _, _, _)    -> m
  | Break m                -> m
  | Continue m             -> m

type top_decl =
  | DDecl   of decl
  | FunDecl of unit meta * name meta * (name meta list * typ) list * typ option * stmts

let top_decl_meta d =
  match d with
  | DDecl d                 -> decl_meta d
  | FunDecl (m, _, _, _, _) -> m

type program = {
    pkg_decl  : string meta;
    top_decls : top_decl list;
  }

let new_selector e1 s =
  Sel(range (expr_meta e1) s (), e1, s.data)

let new_idx e1 e2 i =
  Idx(range (expr_meta e1) i (), e1, e2)

let new_binop op e1 e2 =
  Binop(range (expr_meta e1) (expr_meta e2) op, e1, e2)

let new_uniop op e =
  Uniop(range op (expr_meta e) op.data, e)

let new_app f es r =
  App(range (expr_meta f) r (), f, es)

let rec check_continue_break_stmt inswitch (s : stmt) =
  match s with
  | Simpl _                  -> ()
  | Decl _                   -> ()
  | Block ss                 -> check_continue_break_stmts inswitch ss
  | Print _                  -> ()
  | Println _                -> ()
  | Return _                 -> ()
  | If (_, _, _, tr, fl)     ->
     check_continue_break_stmts inswitch tr;
     begin match fl with
     | None    -> ()
     | Some fl -> check_continue_break_stmts inswitch fl
     end
  | Switch (_, _, _, cl, df) ->
     List.iter (fun c -> check_continue_break_stmt_list true c.exec) cl;
     begin match df with
     | None    -> ()
     | Some df -> check_continue_break_stmt_list true df
     end
  | For (_, _, _, _, ss)     -> ()
  | Break m                  ->
     if inswitch then ()
     else raise (BreakMustInLoop m)
  | Continue m               ->
     raise (ContinueMustInLoopOrSwitch m)
and check_continue_break_stmts inswitch ss =
  (check_continue_break_stmt_list inswitch) ss.data
and check_continue_break_stmt_list inswitch ss =
  List.iter (check_continue_break_stmt inswitch) ss

let check_continue_break p =
  let check_decl d =
    match d with
    | DDecl _                  -> ()
    | FunDecl (_, _, _, _, ss) -> check_continue_break_stmts false ss in
  List.iter check_decl p.top_decls;
  p

(* we need to remove parentheses because they are redundant *)
let rec remove_paren_expr (e : expr) =
  match e with
  | App (m, e, es)     ->  App (m, remove_paren_expr e, remove_paren_exprs es)
  | Sel (m, e, s)      -> Sel (m, remove_paren_expr e, s)
  | Idx (m, e1, e2)    -> Idx (m, remove_paren_expr e1, remove_paren_expr e2)
  | Binop (op, e1, e2) -> Binop (op, remove_paren_expr e1, remove_paren_expr e2)
  | Uniop (op, e)      -> Uniop (op, remove_paren_expr e)
  | Paren e            -> remove_paren_expr e
  | e                  -> e
and remove_paren_exprs es = List.map remove_paren_expr es

let remove_paren_simp_stmt (s : simp_stmt) =
  match s with
  | FApp (m, f, es)            -> FApp (m, remove_paren_expr f, remove_paren_exprs es)
  | Incr e                     -> Incr (update_data e (remove_paren_expr e.data))
  | Decr e                     -> Decr (update_data e (remove_paren_expr e.data))
  | Assign (m, es1, es2)       -> Assign (m, remove_paren_exprs es1, remove_paren_exprs es2)
  | AssignOp (m, e1, op, e2)   -> AssignOp (m, remove_paren_expr e1, op, remove_paren_expr e2)
  | ShortDecl (m, ns, es)      -> ShortDecl (m, ns, remove_paren_exprs es)
  | _                          -> s

let remove_paren_decl (d : decl) =
  match d with
  | VarDecl (m, ns, t, es) -> VarDecl (m, ns, t, remove_paren_exprs es)
  | VarDecls ds            -> VarDecls (update_data ds (List.map (fun (m, ns, t, es) -> (m, ns, t, remove_paren_exprs es)) ds.data))
  | d                      -> d

let rec remove_paren_stmt (s : stmt) =
  match s with
  | Simpl s                  -> Simpl (remove_paren_simp_stmt s)
  | Decl d                   -> Decl (remove_paren_decl d)
  | Block ss                 -> Block (remove_paren_stmts ss)
  | Print es                 -> Print (update_data es (remove_paren_exprs es.data))
  | Println es               -> Println (update_data es (remove_paren_exprs es.data))
  | Return eo                -> Return (update_data eo (Option.map remove_paren_expr eo.data))
  | If (m, s, e, ss1, ss2)   -> If (m, remove_paren_simp_stmt s, remove_paren_expr e, remove_paren_stmts ss1, Option.map remove_paren_stmts ss2)
  | Switch (m, s, e, cs, df) -> Switch (m, remove_paren_simp_stmt s, remove_paren_expr e, List.map remove_paren_case cs, Option.map remove_paren_stmt_list df)
  | For (m, s1, e, s2, ss)   -> For (m, remove_paren_simp_stmt s1, Option.map remove_paren_expr e, remove_paren_simp_stmt s2, remove_paren_stmts ss)
  | _                        -> s
and remove_paren_stmt_list ss = List.map remove_paren_stmt ss
and remove_paren_stmts ss     = update_data ss (remove_paren_stmt_list ss.data)
and remove_paren_case cs      = { cond = remove_paren_exprs cs.cond; exec = remove_paren_stmt_list cs.exec }

let remove_paren_top_decl (d : top_decl) =
  match d with
  | DDecl d                   -> DDecl (remove_paren_decl d)
  | FunDecl (m, n, sg, t, ss) -> FunDecl (m, n, sg, t, remove_paren_stmts ss)

let remove_paren p =
  { p with top_decls = List.map remove_paren_top_decl p.top_decls }
