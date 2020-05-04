open Meta
open Tags
open Syntax
open Repr
open Utils

type typ =
  | Tvoid                       (* instead of returning nothing, we return a void *)
  | Tstr | Tint | Tfloat | Trune | Tbool
  | Tref    of string meta * typ Lazy.t (* refer to a type defined in the meta and resolve to the typ *)
  | Tslice  of typ
  | Tarray  of Int32.t * typ
  | Tstruct of (name * typ) list (* we use list because we still want to keep track of the alignment *)
  | Tfun    of typ list * typ

let resolved_typ (t : typ) =
  match t with
  | Tref (_, t) -> Lazy.force t
  | _           -> t

let resolved_typ_l (t : typ) : typ Lazy.t =
  match t with
  | Tref (_, t) -> t
  | _           -> Lazy.from_val t

let numerics = [Tint ; Tfloat ; Trune]

let is_numeric t = List.mem t numerics

let bases = [Tstr ; Tint ; Tfloat ; Trune ; Tbool]

let is_base t = List.mem t bases

let integers = [Tint ; Trune]

let is_integer t = List.mem t integers

(** note that slices are not comparable *)
let rec is_comparable t =
  match t with
  | Tbool | Tint | Tfloat
    | Trune | Tstr    -> true
  | Tstruct fs        ->
     List.for_all (fun (_, t) -> is_comparable t) fs
  | Tarray (_, t)     ->
     is_comparable t
  | Tref (_, lazy rt) ->
     (* this terminates because slice gives false and won't recurse down *)
     is_comparable rt
  | _                 -> false

let ordereds = [Tint ; Tfloat ; Trune ; Tstr]

(** note that slices and arrays are not ordered *)
let is_ordered t = List.mem t ordereds

let is_assignable (t : typ) =
  match t with
  | Tvoid | Tfun (_, _) -> false
  | _                   -> true

let is_func t =
  match t with
  | Tfun _ -> true
  | _      -> false

let is_struct t =
  match t with
  | Tstruct _ -> true
  | _         -> false

let rec (===) (t1 : typ) (t2 : typ) =
  t1 == t2 ||    
    match t1, t2 with
    | Tvoid           , Tvoid           -> true
    | Tstr            , Tstr            -> true
    | Tint            , Tint            -> true
    | Tfloat          , Tfloat          -> true
    | Trune           , Trune           -> true
    | Tbool           , Tbool           -> true
    | Tref (n1, _)    , Tref (n2, _)    -> n1 = n2 (* we do not compare resolved types *)
    | Tslice t1       , Tslice t2       -> t1 === t2
    | Tarray (s1, t1) , Tarray (s2, t2) -> s1 = s2 && t1 === t2
    | Tstruct nts1    , Tstruct nts2    ->
       Core.List.equal (fun (n1, t1) (n2, t2) -> n1 = n2 && t1 === t2) nts1 nts2
    | Tfun (ts1, r1)  , Tfun (ts2, r2)  ->
       Core.List.equal (===) ts1 ts2 && r1 === r2
    | _               , _               -> false

let (<!>) t1 t2 : bool = not (t1 === t2)

let typ_pprint (t : typ) =
  let rec iter t =
    match t with
    | Tvoid         -> "<none>"
    | Tstr          -> "string"
    | Tint          -> "int"
    | Tfloat        -> "float64"
    | Trune         -> "rune"
    | Tbool         -> "bool"
    | Tref (x, _)   -> x.data
    | Tslice t      -> "[]" ^ iter t
    | Tarray (n, t) -> Format.sprintf "[%s]%s" (Int32.to_string n) (iter t)
    | Tstruct fs    -> Format.sprintf "struct { %s }"
                                      (String.concat " " (List.map (fun (n, t) -> Format.sprintf "%s %s;" (name_str n) (iter t)) fs))
    | Tfun (ts, r)  ->
       match r with
       | Tvoid -> Format.sprintf "func(%s)" (comma_concat iter ts)
       | _     -> Format.sprintf "func(%s) %s" (comma_concat iter ts) (iter r) in
  match t with
  | Tref (x, lazy t) -> Format.sprintf "%s (resolved to %s)" x.data (iter t)
  | _                -> iter t

let find_field f (fs : (name * typ) list) : (int * typ) option =
  let rec find fs acc =
    match fs with
    | []               -> None
    | (Blank, _) :: fs -> find fs (acc + 1)
    | (X x, t) :: fs   ->
       if x = f then Some (acc, t)
       else find fs (acc + 1)
  in
  find fs 0

type expr =
  | GVar   of string meta * typ
  | LVar   of string meta * int * typ
  | Int    of int_kind * string meta
  | Float  of float_kind * string meta
  | Bool   of bol meta
  | Rune   of string * char meta
  (** first string is the input representation while the second one is the interpreted
   * representation. *)
  | String of str_kind * string * string meta
  (** e0(e1, e2, ... , en)  *)
  | App    of unit meta * expr * expr list * typ
  | Append of unit meta * expr * expr
  | Cap    of unit meta * expr
  | Len    of unit meta * expr
  | Cast   of unit meta * string meta * expr * typ
  | Sel    of unit meta * expr * int * string * typ
  (** e1[ e2 ] *)
  | Idx    of unit meta * expr * expr * typ
  | Binop  of binop meta * expr * expr * typ
  | Uniop  of uniop meta * expr * typ

(** whether an expression is a literal *)
let is_lit (e : expr) =
  match e with
  | Int _ | Float _ | Rune _ | String _ -> true
  | _                                   -> false

let is_true (e : expr) =
  match e with
  | Bool b -> b.data = True
  | _      -> false
  
let rec get_typ (e : expr) =
  match e with
  | GVar (_, t)         -> t
  | LVar (_, _, t)      -> t
  | Int (_, _)          -> Tint
  | Float (_, _)        -> Tfloat
  | Bool _              -> Tbool
  | Rune (_, _)         -> Trune
  | String (_, _, _)    -> Tstr
  | App (_, _, _, t)    -> t
  | Append (_, e1, _)   -> get_typ e1
  | Cap (_, _)          -> Tint
  | Len (_, _)          -> Tint
  | Cast (_, _, _, t)   -> t
  | Sel (_, _, _, _, t) -> t
  | Idx (_, _, _, t)    -> t
  | Binop (_, _, _, t)  -> t
  | Uniop (_, _, t)     -> t

let expr_meta (e : expr) =
  match e with
  | GVar (x, _)         -> forget_data x
  | LVar (x, _, _)      -> forget_data x
  | Int (_, i)          -> forget_data i
  | Float (_, f)        -> forget_data f
  | Bool b              -> forget_data b
  | Rune (_, c)         -> forget_data c
  | String (_, _, s)    -> forget_data s
  | App (m, _, _, _)    -> m
  | Append (m, _, _)    -> m
  | Cap (m, _)          -> m
  | Len (m, _)          -> m
  | Cast (m, _, _, _)   -> m
  | Sel (m, _, _, _, _) -> m
  | Idx (m, _, _, _)    -> m
  | Binop (op, _, _, _) -> forget_data op
  | Uniop (op, _, _)    -> forget_data op

let rt_expr e = resolved_typ (get_typ e)

let resolve_to_comparable e = is_comparable (get_typ e)

let resolve_to_ordered e = is_ordered (rt_expr e)

let resolve_to_numeric e = is_numeric (rt_expr e)

let resolve_to_integer e = is_integer (rt_expr e)

let rec to_untyped_expr (e : expr) =
  match e with
  | GVar (x, _)           -> Untyped.Var (update_data x (X x.data))
  | LVar (x, _, _)        -> Untyped.Var (update_data x (X x.data))
  | Int (k, i)            -> Untyped.Int (k, i)
  | Float (k, f)          -> Untyped.Float (k, f)
  | Bool b                -> Untyped.Bool b
  | Rune (s, c)           -> Untyped.Rune (s, c)
  | String (k, rs, s)     -> Untyped.String (k, rs, s)
  | App (m, f, es, _)     -> Untyped.App (m, to_untyped_expr f, List.map to_untyped_expr es)
  | Append (m, e1, e2)    -> Untyped.Append (m, to_untyped_expr e1, to_untyped_expr e2)
  | Cap (m, e)            -> Untyped.Cap (m, to_untyped_expr e)
  | Len (m, e)            -> Untyped.Len (m, to_untyped_expr e)
  | Cast (m, t, e, _)     -> Untyped.App (m, Untyped.Var (update_data t (X t.data)), [to_untyped_expr e])
  | Sel (m, e, _, i, _)   -> Untyped.Sel (m, to_untyped_expr e, i)
  | Idx (m, e1, e2, _)    -> Untyped.Idx (m, to_untyped_expr e1, to_untyped_expr e2)
  | Binop (op, e1, e2, _) -> Untyped.Binop (op, to_untyped_expr e1, to_untyped_expr e2)
  | Uniop (op, e, _)      -> Untyped.Uniop (op, to_untyped_expr e)

type ltyp =
  | Any
  | T of typ

type aexpr = 
  | AGVar of string meta * typ
  | ALVar of string meta * int * typ
  | ASel  of unit meta * aexpr * int * string * typ
  | AIdx  of unit meta * aexpr * expr * typ

type lexpr =
  | LBlank of unit meta
  | LAexpr of aexpr

let get_atyp ae =
  match ae with 
  | AGVar (_, t)         -> t
  | ALVar (_, _, t)      -> t
  | ASel (_, _, _, _, t) -> t
  | AIdx (_, _, _, t)    -> t

let aexpr_meta e =
  match e with
  | AGVar (m, _)         -> forget_data m
  | ALVar (m, _, _)      -> forget_data m
  | ASel (m, _, _, _, _) -> m
  | AIdx (m, _, _, _)    -> m

let get_ltyp (lexp : lexpr) : ltyp =
  match lexp with
  | LBlank _  -> Any
  | LAexpr ae -> T (get_atyp ae)

let rec to_untyped_aexpr (e : aexpr) =
  match e with
  | AGVar (x, _)         -> Untyped.Var (update_data x (X x.data))
  | ALVar (x, _, _)      -> Untyped.Var (update_data x (X x.data))
  | ASel (m, e, _, i, _) -> Untyped.Sel (m, to_untyped_aexpr e, i)
  | AIdx (m, e1, e2, _)  -> Untyped.Idx (m, to_untyped_aexpr e1, to_untyped_expr e2)

let to_untyped_lexpr (e : lexpr) =
  match e with
  | LBlank m -> Untyped.Var (update_data m Blank)
  | LAexpr e -> to_untyped_aexpr e

let rec aexpr_to_expr (e : aexpr) =
  match e with
  | AGVar (x, t)         -> GVar (x, t)
  | ALVar (x, i, t)      -> LVar (x, i, t)
  | ASel (m, e, i, x, t) -> Sel (m, aexpr_to_expr e, i, x, t)
  | AIdx (m, e1, e2, t)  -> Idx (m, aexpr_to_expr e1, e2, t)

(** 'a tracks what identifies a variable *)
type 'a decl =
  (* var decl which has no ascribed type *)
  | VarDecl1 of unit meta * ('a gname meta * expr) list
  (* var decl which has an ascribed type but no exprs *)
  | VarDecl2 of unit meta * 'a gname meta list * typ
  (* var decl which has both an ascribed type and exprs *)
  | VarDecl3 of unit meta * ('a gname meta * expr) list * typ
  | TypDecl  of unit meta * string meta * typ

(** global declarations *)
type gdecl = string decl

(** local declarations *)
type ldecl = int decl

let decl_meta (d : 'a decl) =
  match d with
  | VarDecl1 (m, _)    -> m
  | VarDecl2 (m, _, _) -> m
  | VarDecl3 (m, _, _) -> m
  | TypDecl (m, _, _)  -> m

type sname =
  | SBlank
  | Existed of int
  | New     of int

let new_lname (n : lname) =
  match n with
  | Blank -> SBlank
  | X i   -> New i

let existed_lname (n : lname) =
  match n with
  | Blank -> SBlank
  | X i   -> Existed i
             
let is_new (s : sname) =
  match s with
  | New _ -> true
  | _     -> false
             
type simp_stmt =
  | Nop       of unit meta
  | FApp      of unit meta * expr * expr list * typ
  | Incr      of aexpr meta
  | Decr      of aexpr meta
  | Assign    of unit meta * (lexpr * expr) list
  | AssignOp  of unit meta * aexpr * arith * expr
  | ShortDecl of unit meta * (sname meta * expr) list

let simp_stmt_meta (s : simp_stmt) =
  match s with
  | Nop m                 -> m
  | FApp (m, _, _, _)     -> m
  | Incr e                -> forget_data e
  | Decr e                -> forget_data e
  | Assign (m, _)         -> m
  | AssignOp (m, _, _, _) -> m
  | ShortDecl (m, _)      -> m

type case = {
    cond : expr list;
    exec : stmt list
  }
and stmt =
  | Simpl    of simp_stmt
  | Decl     of ldecl
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

let stmt_meta (s : stmt) =
  match s with
  | Simpl s                -> simp_stmt_meta s
  | Decl d                 -> decl_meta d
  | Block ss               -> stmts_meta ss
  | Print es               -> forget_data es
  | Println es             -> forget_data es
  | Return e               -> forget_data e
  | If (m, _, _, _, _)     -> m
  | Switch (m, _, _, _, _) -> m
  | For (m, _, _, _, _)    -> m
  | Break m                -> m
  | Continue m             -> m

type lv_list = (string * typ) list

type top_decl =
  | DDecl   of gdecl
  | FunDecl of unit meta * name meta * (lname meta * typ) list * typ * lv_list * stmts

let top_decl_meta d =
  match d with
  | DDecl d                    -> decl_meta d
  | FunDecl (m, _, _, _, _, _) -> m

type program = {
    pkg_decl  : string meta;
    top_decls : top_decl list;
  }
