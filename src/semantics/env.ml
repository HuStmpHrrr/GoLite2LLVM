open Typed
open Common
open Utils
open Meta

type kind =
  | Gbnd   of typ
  | Lbnd   of int * typ
  | BConst of bol
  | Func   of typ
  | Tbnd   of typ
  | Alias  of typ

type frame = (kind * unit meta) SMap.t (* meta keeps track of where a binding is introduced *)
type env = frame * frame list   (* a tuple like this is a non-empty list *)

exception Redecl of string meta * kind * unit meta

let default_env : env = SMap.empty,
                  [SMap.of_alist_reduce
                     ~f:(fun _ x -> x)
                     [ "true"    , (BConst True  , meta_zero)
                     ; "false"   , (BConst False , meta_zero)
                     ; "int"     , (Alias Tint   , meta_zero)
                     ; "float64" , (Alias Tfloat , meta_zero)
                     ; "rune"    , (Alias Trune  , meta_zero)
                     ; "bool"    , (Alias Tbool  , meta_zero)
                     ; "string"  , (Alias Tstr   , meta_zero)]]
         
let empty_env : env = SMap.empty, []

let new_frame ((top, stack) : env) : env = SMap.empty, top :: stack

let top_frame (e : env) = fst e

let find_opt k (e : env) =
  let rec iter fs =
    match fs with
    | []      -> None
    | f :: fs -> 
       match SMap.find f k with
       | None   -> iter fs
       | Some v -> Some v in
  match SMap.find (top_frame e) k with
  | None   -> iter (snd e)
  | Some v -> Some v

type add_res =
  | Found of string meta * kind * unit meta
  | New   of env

let add_opt n k (e : env) : add_res =
  match SMap.add (top_frame e) ~key:n.data ~data:(k, forget_data n) with
  | `Ok r      -> New (r, snd e)
  | `Duplicate ->
     let (k, m) = SMap.find_exn (top_frame e) n.data in
     Found (n, k, m)

let rec add_all_opt bs (e : env) : add_res =
  match bs with
  | []           -> New e
  | (n, v) :: bs ->
     match add_opt n v e with
     | New e'          -> add_all_opt bs e'
     | Found (n, k, m) -> Found (n, k, m)
