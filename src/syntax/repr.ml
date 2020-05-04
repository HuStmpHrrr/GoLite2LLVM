open Meta
open Ast
open Format
open Utils
open Common

open Modules

exception UnknownChar of char

let ari_str op =
  match op with
  | Plus   -> "+"
  | Minus  -> "-"
  | Times  -> "*"
  | Div    -> "/"
  | Rem    -> "%"
  | Band   -> "&"
  | Bor    -> "|"
  | Bxor   -> "^"
  | Lshift -> "<<"
  | Rshift -> ">>"
  | Bclear -> "&^"

let log_str op =
  match op with
  | And -> "&&"
  | Or  -> "||"
  | Eq  -> "=="
  | Neq -> "!="
  | Ge  -> ">="
  | Le  -> "<="
  | Gt  -> ">"
  | Lt  -> "<"

let bin_str op =
  match op with
  | Ar op -> ari_str op
  | Lo op -> log_str op

let uni_str op =
  match op with
  | Pos   -> "+"
  | Neg   -> "-"
  | Not   -> "!"
  | Bcomp -> "^"
           
let name_str x =
  match x with
  | Blank -> "_"
  | X x   -> x

let precedence op =
  match op with
  | Ar op ->
     begin match op with
     | Plus   -> 4
     | Minus  -> 4
     | Times  -> 5
     | Div    -> 5
     | Rem    -> 5
     | Band   -> 5
     | Bor    -> 4
     | Bxor   -> 4
     | Lshift -> 5
     | Rshift -> 5
     | Bclear -> 5
     end
  | Lo op ->
     begin match op with
     | And -> 2
     | Or  -> 1
     | Eq  -> 3
     | Neq -> 3
     | Ge  -> 3
     | Le  -> 3
     | Gt  -> 3
     | Lt  -> 3
     end

let pred_bot = 0
let pred_top = 6

let indent_level = "    "

(** [expr_pprint] and [expr_pprint_paren] both pretty-print an [expr].
 *
 * The difference is that [expr_pprint_paren] conservatively inserts an outer pair of
   parentheses when necessary.
 *)
let expr_pprint, expr_pprint_paren =
  let rec iter (e : expr) p l =
    match e with
    | Var x              -> name_str x.data
    | Int (_, i)         -> i.data
    | Float (_, f)       -> f.data
    | Bool b             ->
       begin match b.data with
       | True  -> "true"
       | False -> "false"
       end
    | Rune (s, _)        -> s
    | String (_, r, _)   -> r
    | App (_, e, es)     ->
       sprintf "%s(%s)" (expr_pprint_paren' e)
               (comma_concat expr_pprint_noparen es)
    | Append (_, e1, e2) ->
       sprintf "append(%s)" (expr_pprint_noparen e)
    | Len (_, e)         ->
       sprintf "len(%s)" (expr_pprint_noparen e)
    | Cap (_, e)         ->
       sprintf "cap(%s)" (expr_pprint_noparen e)
    | Sel (_, e, f)     -> expr_pprint_paren' e ^ "." ^ f
    | Idx (_, e1, e2)    ->
       let s1 = expr_pprint_paren' e1
       and s2 = expr_pprint_noparen e2 in
       sprintf "%s[%s]" s1 s2
    | Binop (op, e1, e2) ->
       let p' = precedence op.data in
       let s1 = iter e1 p' true
       and s2 = iter e2 p' false in
       if p' < p || p = p' && not l then
         sprintf "(%s %s %s)" s1 (bin_str op.data) s2
       else
         sprintf "%s %s %s" s1 (bin_str op.data) s2
    | Uniop (op, e)      ->
       let default pad =
         if p > pred_top then
           sprintf "(%s)" (uni_str op.data ^ pad ^ expr_pprint_paren e)
         else uni_str op.data ^ pad ^ expr_pprint_paren e in
       begin match e with
       | Uniop (op2, e) ->
          if (op.data = Pos) && (op2.data = Pos) then
            default "(" ^ ")"
          else if (op.data = Neg) && (op2.data = Neg) then
            default "(" ^ ")"
          else
            default ""
       | _ -> default ""
       end
    | Paren e            -> sprintf "(%s)" (iter e p l)
  and expr_pprint_paren e   = iter e pred_top false
  and expr_pprint_paren' e  = iter e (1 + pred_top) false
  and expr_pprint_noparen e = iter e pred_bot true in
  expr_pprint_noparen, expr_pprint_paren

(** returns (h, tl) which is meant to be a non-empty list *)
let typ_pprint t indent =
  let rec helper t indent = 
    match t with
    | Tref t           -> t.data, []
    | Tslice (_, t)    ->
       let h, tl = helper t indent in
       "[]" ^ h, tl
    | Tarray (_, _, i, t) ->
       let h, tl = helper t indent in
       sprintf "[%s]%s" i.data h, tl
    | Tstruct (_, ts)  ->
       "struct {", List.append (struct_helper ts (indent_level ^ indent)) [indent ^ "}"]
  and struct_helper ts indent =
    match ts with
    | []            -> []
    | (ns, t) :: ts ->
       List.append
         begin
           let h, tl = helper t indent in
           match ns with
           | []     -> (indent ^ h) :: tl
           | _ :: _ -> (indent ^ sprintf "%s %s" (comma_concat (fun n -> name_str n.data) ns) h) :: tl
         end
         (struct_helper ts indent) in
  helper t indent

let simp_stmt_pprint s =
  match s with
  | Nop _                      -> ""
  | FApp (m, f, es)            -> expr_pprint (App (m, f, es))
  | Incr e                     -> expr_pprint_paren e.data ^ "++"
  | Decr e                     -> expr_pprint_paren e.data ^ "--"
  | Assign (_, es1, es2)       ->
     sprintf "%s = %s" (comma_concat expr_pprint es1) (comma_concat expr_pprint es2)
  | AssignOp (_, e1, op, e2)   ->
     sprintf "%s %s= %s" (expr_pprint e1) (ari_str op) (expr_pprint e2)
  | ShortDecl (_, ns, es)      ->
     sprintf "%s := %s" (comma_concat (fun n -> name_str n.data) ns) (comma_concat expr_pprint es)

let decl_pprint d indent =
  let vdecl ns t es indent =
    let ns_str = comma_concat (fun n -> name_str n.data) ns
    and es_str =
      match es with
      | []     -> ""
      | _ :: _ -> " = " ^ comma_concat expr_pprint es in
    match t with
    | None   ->
       sprintf "%s%s" ns_str es_str, []
    | Some t ->
       let h, tl = typ_pprint t indent in
       match init_last tl with
       | None ->
          sprintf "%s %s%s" ns_str h es_str, []
       | Some (l, th) ->
          sprintf "%s %s" ns_str h, th @ [sprintf "%s%s" l es_str]
  and tdecl n t indent =
    let h, tl = typ_pprint t indent in
    ((name_str n.data) ^ " " ^ h), tl
  in
  match d with
  | VarDecl (_, ns, t, es) ->
     let h, tl = vdecl ns t es indent in
     (indent ^ "var " ^ h) :: tl
  | VarDecls vs            ->
     begin match vs.data with
     | []     -> [indent ^ "var ()"]
     | _ :: _ ->
        let indent' = indent_level ^ indent in
        let vdecl' (m, ns, t, es) =
          let h, tl = vdecl ns t es indent' in
          (indent' ^ h) :: tl in
        (indent ^ "var (")
        :: (List.bind vs.data ~f:vdecl')
        @ [indent ^ ")"]
     end
  | TypDecl (_, n, t)      ->
     let h, tl = tdecl n t indent in
     (indent ^ "type " ^ h) :: tl
  | TypDecls ts            ->
     match ts.data with
     | []     -> [indent ^ "type ()"]
     | _ :: _ ->
        let indent' = indent_level ^ indent in
        let tdecl' (m, n, t) =
          let h, tl = tdecl n t indent' in
          (indent' ^ h) :: tl in
        (indent ^ "type (")
        :: (List.bind ts.data ~f:tdecl')
        @ [indent ^ ")"]

let rec case_pprint {cond; exec} indent =
  (indent ^ sprintf "case %s:" (comma_concat expr_pprint cond))
  :: stmt_list_pprint exec (indent_level ^ indent)
and stmt_pprint (s : stmt) indent =
  match s with
  | Simpl s                   -> if is_nop s then [] else [indent ^ simp_stmt_pprint s]
  | Decl d                    -> decl_pprint d indent
  | Block ss                  ->
     (indent ^ "{") :: stmts_pprint ss (indent_level ^ indent) @ [indent ^ "}"]
  | Print es                  -> [indent ^ sprintf "print(%s)" (comma_concat expr_pprint es.data)]
  | Println es                -> [indent ^ sprintf "println(%s)" (comma_concat expr_pprint es.data)]
  | Return eo                 ->
     begin match eo.data with
     | None   -> [indent ^ "return"]
     | Some e -> [indent ^ "return " ^ expr_pprint e]
     end
  | If (_, s, e, t, f)        ->
     let indent'  = indent_level ^ indent
     and head s e =
       if is_nop s then
         sprintf "if %s {" (expr_pprint e)
       else
         sprintf "if %s; %s {" (simp_stmt_pprint s) (expr_pprint e) in
     let rec fcase f =
       match f with
       | Some ss ->
          begin match ss.data with
          | [] -> [indent ^ "} else { }"]
          | [If (_, s, e, t, f)] ->
             (indent ^ "} else " ^ head s e) :: stmts_pprint t indent' @ fcase f
          | _ :: _ ->
             (indent ^ "} else {") :: stmts_pprint ss indent' @ [indent ^ "}"]
          end
       | None -> [indent ^ "}"] in
     (indent ^ head s e) :: stmts_pprint t indent' @ fcase f
  | Switch (_, s, e, cs, dfl) ->
     let no_init = is_nop s
     and no_e    = is_true e
     and indent' = indent_level ^ indent in
     let head    =
       indent ^ "switch "
       ^ (if no_init then "" else simp_stmt_pprint s ^ "; ")
       ^ (if no_e then "{" else expr_pprint e ^ " {") in
     begin match cs with
     | []     -> [head ^ " }"]
     | _ :: _ ->
        head :: List.bind cs ~f:(fun c -> case_pprint c indent') @ [indent ^ "}"]
     end
  | For (_, s1, e, s2, ss)    ->
     let indent' = indent_level ^ indent in
     let head   =
       if is_nop s1 && is_nop s2 then
         match e with
         | None   -> 
           indent ^ "for {"
         | Some e ->
           indent ^ sprintf "for %s {" (expr_pprint e)
       else
         indent ^ sprintf "for %s; %s; %s {"
                          (simp_stmt_pprint s1)
                          (match e with | None -> "" | Some e -> expr_pprint e)
                          (simp_stmt_pprint s2) in
     begin match ss.data with
     | []     -> [head ^ " }"]
     | _ :: _ -> head :: stmts_pprint ss indent' @ [indent ^ "}"]
     end 
  | Break _                   -> [indent ^ "break"]
  | Continue _                -> [indent ^ "continue"]
and stmt_list_pprint ss indent = List.bind ss ~f:(fun s -> stmt_pprint s indent)
and stmts_pprint ss indent     = stmt_list_pprint ss.data indent

let top_decl_pprint td =
  match td with
  | DDecl d                       ->
     decl_pprint d "" @ [""]
  | FunDecl (_, f, vss, rt, body) ->
     let chunk_str (vs, t) last =
       let h, tl = typ_pprint t indent_level in
       let first = indent_level ^ comma_concat (fun v -> name_str v.data) vs ^ " " ^ h in
       match init_last tl with
       | None          -> [first ^ last]
       | Some (l, tl') -> first :: tl' @ [l ^ last] in
     let head =
       let param_list_str last =
         match init_last vss with
         | None         -> [sprintf "func %s()%s" (name_str f.data) last]
         | Some (l, tl) ->
            sprintf "func %s(" (name_str f.data) ::
              List.bind tl ~f:(fun vst -> chunk_str vst ",")
            @ chunk_str l (")" ^ last) in
       match rt with
       | None   ->
          param_list_str " {"
       | Some t ->
          let h, tl = typ_pprint t indent_level in
          match init_last tl with
          | None          -> param_list_str (sprintf " %s {" h)
          | Some (l, tl') -> param_list_str (" " ^ h) @ tl' @ [l ^ " {"] in
     head @ stmts_pprint body indent_level @ ["}"; ""]

let program_pprint prog =
  ("package " ^ prog.pkg_decl.data)
  :: ""
  :: List.bind prog.top_decls ~f:top_decl_pprint

module Abandoned = struct  
  let escape_rune c =
    match c with
    | '\x07'     -> "\\a"
    | '\x06'     -> "\\b"
    | '\x0c'     -> "\\f"
    | '\n'       -> "\\n"
    | '\r'       -> "\\r"
    | '\t'       -> "\\t"
    | '\x0b'     -> "\\v"
    | '\\'       -> "\\\\"
    | '\''       -> "\\'"
    | ' ' .. '~' -> Char.to_string c
    | _          ->
       let rec iter n =
         if n = 0 then []
         else n mod 16 :: iter (n / 16) in
       let rec dgs ds s =
         match ds with
         | []      -> s
         | d :: ds -> dgs ds (s ^ sprintf "%x" d) in
       let ds = iter (Char.to_int c) in
       let l  = List.length ds
       and cs = dgs ds "" in
       if l <= 2 then
         "\\x" ^ String.init (2 - l) ~f:(fun _ -> '0') ^ cs
       else if l <= 4 then
         "\\u" ^ String.init (4 - l) ~f:(fun _ -> '0') ^ cs
       else if l <= 8 then
         "\\U" ^ String.init (8 - l) ~f:(fun _ -> '0') ^ cs
       else raise (UnknownChar c)

  let rune_str c = sprintf "'%s'" (escape_rune c)

  let escape_str s =
    String.fold s ~init:"" ~f:(fun acc c -> acc ^ escape_rune c)
  
end
