open Env
open Syntax
open Typed
open Meta

type exenv = {
    underl : env;               (* underlying env *)
    size   : int;               (* size of the local variable stack *)
    locals : lv_list;
  }

type _ decl_env =
  | Global : env -> string decl_env
  | Local  : exenv -> int decl_env

let underl_env (type t) (g : t decl_env) : env =
  match g with
  | Global g -> g
  | Local g  -> g.underl

let update_underl_env (type t) (g : t decl_env) (e : env) : t decl_env =
  match g with
  | Global g -> Global e
  | Local g  -> Local { g with underl = e }

let exenv_new_frame (g : exenv) =
  { g with underl = new_frame g.underl }

let update_locals (g : exenv) (g' : exenv) =
  { g' with underl = g.underl }
  
let from_local (g : int decl_env) : exenv =
  match g with | Local g -> g

let extend (g : env) =
  {
    underl = g;
    size   = 0;
    locals = [];
  }
                          
type 'a add_name_res = [
  | `Ok of 'a decl_env * 'a gname meta
  | `Found of string meta * kind * unit meta
  ]

let add_name_bnd_s (type t) (g : t decl_env) (n : name meta) (t : typ) : t add_name_res =
  match n.data with
  | Blank -> `Ok (g, update_data n Blank)
  | X x   ->
     match g with
     | Global ug ->
        let k = Gbnd t in
        begin match add_opt (update_data n x) k ug with
        | New g'          -> `Ok (Global g', update_data n (X x))
        | Found (n, k, m) -> raise (Redecl (n, k, m))
        end
     | Local eg  ->
        let i = eg.size in
        let k = Lbnd (i, t) in
        match add_opt (update_data n x) k eg.underl with
        | New g'          ->
           `Ok (Local {
                    underl = g';
                    size   = i + 1;
                    locals = (x, t) :: eg.locals;
                  }, update_data n (X i)) 
        | Found (n, k, m) -> `Found (n, k, m)
                    
let add_name_bnd (type t) (g : t decl_env) (n : name meta) (t : typ) : t decl_env * t gname meta =
  match add_name_bnd_s g n t with
  | `Ok (g, n)       -> g, n
  | `Found (n, k, m) -> raise (Redecl (n, k, m))

let add_names_bnds (type t) (g : t decl_env) (bs : (name meta * typ) list) =
  Core.List.fold_map bs ~init:g ~f:(fun g (n, t) -> add_name_bnd g n t)

let add_name_kind (g : env) (n : name meta) (k : kind) =
  match n.data with
  | Blank -> g
  | X x   ->
     match add_opt (update_data n x) k g with
     | New g'          -> g'
     | Found (n, k, m) -> raise (Redecl (n, k, m))
