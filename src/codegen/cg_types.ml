open Syntax
open Typed
open Cg_common

module Make (X : CgEnv) = struct
  open X
  open Basics (X)
  open Cg_generate.Make (X)

  let rec codegen_typ (t : typ) : lltype =
    let fields fs =
      Array.of_list (List.map (fun (_, t) -> codegen_typ t) fs) in
    match t with
    | Tvoid             -> void_type
    | Tstr              -> str_type
    | Tint              -> int_type
    | Tfloat            -> float_type
    | Trune             -> rune_type
    | Tbool             -> bool_type
    | Tref (x, lazy rt) ->
       begin match rt with
       | Tstruct fs ->
          begin match named_struct x with
          | None   ->
             let s = named_struct_type g.context (ty_name x) in
             struct_set_body s (fields fs) false;
             s
          | Some t -> t
          end
       | _          -> codegen_typ rt
       end
    | Tslice _          -> slice_type ()
    | Tarray (n, t)     -> array_type (codegen_typ t) (Int32.to_int n)
    | Tstruct fs        ->
       struct_type g.context (fields fs)
    | Tfun (ts, rt)     ->
       function_type (codegen_typ rt) (Array.of_list (List.map codegen_typ ts))

  let rec encode_typ (t : typ) : string =
    match t with
     | Tvoid             -> ""  (* we won't need it *)
     | Tstr              -> "S"
     | Tint              -> "I"
     | Tfloat            -> "F"
     | Trune             -> "I"
     | Tbool             -> "B"
     | Tref (x, lazy rt) ->
        begin match rt with
        | Tstruct _ -> Format.sprintf "R$%sC$" (ty_name x)
        | _         -> encode_typ rt
        end
     | Tslice _          -> "L"
     | Tarray (n, t)     -> Format.sprintf "A$%s_%sC$" (Int32.to_string n) (encode_typ t)
     | Tstruct fs        -> Format.sprintf "X$%sC$" (String.concat "" (List.map (fun (_, t) -> encode_typ t) fs))
     | Tfun (ts, rt)     -> ""  (* we won't need it *)

  let is_aggregate t =
    match resolved_typ t with
    | Tarray _
      | Tstruct _ -> true
    | _           -> false
      
  let param_typ t : lltype =
    let t' = codegen_typ t in
    if is_aggregate t then pointer_type t'
    else t'

  (** if a function as an array or a struct as return type, then it comes the last
     param and passed by pointer *)
  let func_type ts rt : lltype =
    let pts = List.map param_typ ts in
    let rt' = param_typ rt in
    if is_aggregate rt then
      function_type void_type (Array.of_list (pts @ [rt']))
    else
      function_type rt' (Array.of_list pts)

  (** [pn] denotes the number of parameters *)
  let allocas lv pn : lvenv =
    let func = current_func () in
    let locs = List.mapi (fun i (x, t) ->
                   if is_aggregate t && i < pn then
                     (i, (x, param func i))
                   else 
                     (i, (x, build_alloca (codegen_typ t) (loc_var x) g.builder))) lv in
    Lv.of_alist_reduce ~f:(fun x _ -> x) locs

end
