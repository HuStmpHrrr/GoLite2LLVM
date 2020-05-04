open Golite

open Lexer
open Meta
open Parser
open Tags
open Exec
open Repr
open Codegen
open Utils
open Printf

open Parser_exn
open Error_messages


let help_message = "Please specify a mode: scan | tokens | parse | pretty | typecheck | symbol <file>"

let exit_ok () =
  print_endline "OK";
  exit 0

let tokenizer tkn : string = 
  match tkn with
  | Parser.PACKAGE             -> "tPACKAGE"
  | Parser.IMPORT              -> "tIMPORT"
  | Parser.BLANKIDENT _        -> "tBLANKIDENTIFIER"
  | Parser.IDENT x             -> sprintf "tIDENTIFIER(%s)" x.data
  | Parser.FUNC _              -> "tFUNC"
  | Parser.VAR _               -> "tVAR"
  | Parser.COLON               -> "tCOLON"
  | Parser.COMMA               -> "tCOMMA"
  | Parser.SEMI _
    | Parser.SEMINL _          -> "tSEMICOLON"
  | Parser.IF _                -> "tIF"
  | Parser.ELSE                -> "tELSE"
  | Parser.SWITCH _            -> "tSWITCH"
  | Parser.DEFAULTCASE _       -> "tDEFAULT"  
  | Parser.CASE _              -> "tCASE"
  | Parser.FORLO _             -> "tFOR"
  | Parser.CONTINUE _          -> "tCONTINUE"
  | Parser.FALLTHROUGH         -> "tFALLTHROUGH"
  | Parser.BREAK _             -> "tBREAK"
  | Parser.LPAREN _            -> "tLPAREN"
  | Parser.RPAREN _            -> "tRPAREN"
  | Parser.LSQBRACKET _        -> "tLBRACKET"
  | Parser.RSQBRACKET _        -> "tRBRACKET"
  | Parser.LCBRACKET _         -> "tLBRACE"
  | Parser.RCBRACKET _         -> "tRBRACE"
  | Parser.PLUS _              -> "tPLUS"
  | Parser.MINUS _             -> "tMINUS"
  | Parser.TIMES               -> "tTIMES"
  | Parser.DIV                 -> "tDIV"
  | Parser.MODULE              -> "tREM"  
  | Parser.ASSIGN              -> "tASSIGN"
  | Parser.SHORTASSIGN         -> "tDEFINE"
  | Parser.PLUSASSIGN          -> "tPLUSASSIGN"
  | Parser.TIMESASSIGN         -> "tTIMESASSIGN"
  | Parser.MINUSASSIGN         -> "tMINUSASSIGN"
  | Parser.DIVASSIGN           -> "tDIVASSIGN"
  | Parser.MODULEASSIGN        -> "tREMASSIGN"
  | Parser.BITANDASSIGN        -> "tBWANDASSIGN" 
  | Parser.BITORASSIGN         -> "tBWORASSIGN" 
  | Parser.BITXORASSIGN        -> "tBWXORASSIGN" 
  | Parser.BINLEFTSHIFTASSIGN  -> "tLSHIFTASSIGN" 
  | Parser.BINRIGHTSHIFTASSIGN -> "tRSHIFTASSIGN" 
  | Parser.BITCLRASSIGN        -> "tBWANDNOTASSIGN" 
  | Parser.EQ                  -> "tEQUALS"
  | Parser.NEQ                 -> "tNE" 
  | Parser.GE                  -> "tGE"
  | Parser.LE                  -> "tLE"
  | Parser.GT                  -> "tGT"
  | Parser.LT                  -> "tLT"
  | Parser.AND                 -> "tAND"
  | Parser.OR                  -> "tOR"  
  | Parser.NOT _               -> "tNOT"
  | Parser.BITAND              -> "tBWAND"  
  | Parser.BITOR               -> "tBWOR"
  | Parser.XOR _               -> "tBWXOR"
  | Parser.BINLEFTSHIFT        -> "tLSHIFT"
  | Parser.BINRIGHTSHIFT       -> "tRSHIFT"
  | Parser.BITCLR              -> "tBWANDNOT"
  | Parser.INCR _              -> "tINC"
  | Parser.DECR _              -> "tDEC"
  | Parser.CHANNELOP           -> "tARROW"
  | Parser.VARIADIC            -> "tELLIPSIS"
  | Parser.SELECTOR            -> "tDOT"
  | Parser.INTERFACE           -> "tINTERFACE"
  | Parser.SELECT              -> "tSELECT"
  | Parser.DEFER               -> "tDEFER"
  | Parser.MAP                 -> "tMAP"
  | Parser.STRUCT _            -> "tSTRUCT"
  | Parser.GOSTMT              -> "tGO"
  | Parser.GOTOSTMT            -> "tGOTO"
  | Parser.CHANNEL             -> "tCHAN"
  | Parser.CONST               -> "tCONST"
  | Parser.RANGE               -> "tRANGE"
  | Parser.TYPEKEY _           -> "tTYPE"
  | Parser.PRINT _             -> "tPRINT"
  | Parser.PRINTLN _           -> "tPRINTLN"
  | Parser.APPEND _            -> "tAPPEND"
  | Parser.CAP _               -> "tCAP"
  | Parser.LEN _               -> "tLEN"
  | Parser.RETURN _            -> "tRETURN"
  | Parser.SVAL (_, _, s)      -> sprintf "tSTRINGVAL(%s)" s.data
  | Parser.INTVAL (_, n)       -> sprintf "tINTVAL(%s)" n.data
  | Parser.FVAL (_, n)         -> sprintf "tFLOATVAL(%s)" n.data
  | Parser.RUNEVAL (s, c)      -> sprintf "tRUNEVAL(%c)" c.data
  | Parser.EOF _               -> ""

let parse_loop lexbuf (check : 'a I.checkpoint) =
  let success st = st
  and fail = function
    | I.HandlingError ev ->
       let m = coordinates' lexbuf in
       prerr_string (sprintf "Error: %s: %s" (meta_str m) (message (I.current_state_number ev)));
       exit 1
    | _ ->
       prerr_string "Error: impossible";
       exit 1 in
    I.loop_handle success fail (I.go_lexbuf_to_supplier Lexer.read lexbuf) check

let lexer_catch_exn f =
  try
    f ()
  with LexerError e ->
        die (fun p -> p.fmt "Error: %s: unexpected string \"%s\"" (meta_str e) e.data)
     | UnfinishedComment e ->
        die (fun p -> p.fmt "Error: %s: the general comment is not finished" (meta_str e))
     | NonAsciiChar e ->
        die (fun p -> p.fmt "Error: %s: the following character is not Ascii and therefore not supported: %c" (meta_str e) e.data)
     | UninterpretableEscape e ->
        die (fun p -> p.fmt "Error: %s: the following escape sequence is not supported: %s" (meta_str e) e.data)
     | TooManyForRune e ->
        die (fun p -> p.fmt "Error: %s: rune literal contains too many characters: %s" (meta_str e) e.data)
     | TooFewForRune e ->
        die (fun p -> p.fmt "Error: %s: rune literal contains no character" (meta_str e))
     | UnfinishedRune e ->
        die (fun p -> p.fmt "Error: %s: a rune literal is not finished" (meta_str e))
     | UnfinishedString (k, e) ->
        let knd =
          match k with
          | Sraw -> "a raw"
          | Sint -> "an interpreted" in
        die (fun p -> p.fmt "Error: %s: %s string literal is not finished" (meta_str e) knd)
     | NewLineInInterpreted e ->
        die (fun p -> p.fmt "Error: %s: there is a new line in an interpreted string literal" (meta_str e))

let parser_catch_exn f =
  try
    f ()
  with ShortDeclIdents e ->
        die (fun p -> p.fmt "Error: %s: only an identity is allowed in short declaration"
                            (meta_str (Untyped.expr_meta e)))
     | NotFuncApplication e ->
        die (fun p -> p.fmt "Error: %s: %s is not a function application but appear as a statement"
                            (meta_str (Untyped.expr_meta e)) (expr_pprint_paren (Untyped.remove_paren_expr e)))
     | AtMostOneDefault m ->
        die (fun p -> p.fmt "Error: %s: there must be at most one default case in a switch statement" (meta_str m))
     | BreakMustInLoop m ->
        die (fun p -> p.fmt "Error: %s: a break statement must be inside of a loop body" (meta_str m))
     | ContinueMustInLoopOrSwitch m ->
        die (fun p -> p.fmt "Error: %s: a continue statement must be inside of a loop or a switch" (meta_str m))
     | ForPostNoShortDecl s ->
        die (fun p -> p.fmt "Error: %s: short declaration cannot appear as a post statement of a for loop"
                            (meta_str (Untyped.simp_stmt_meta s)))

let emeta_str e = meta_str (expr_meta e)

let texpr_pprint e = expr_pprint_paren (to_untyped_expr e)

let etyp_pprint e = Typed.typ_pprint (get_typ e)

let tc_catch_exn f =
  try
    f ()
  with InvalidBlankLocation m ->
        die (fun p -> p.fmt "Error: %s: '_' appears in an invalid location" (meta_str m))
     | VariableNotFound x ->
        die (fun p -> p.fmt "Error: %s: variable %s is not bound" (meta_str x) x.data)
     | DuplicateField (t, f1, f2) ->
        die (fun p -> p.fmt "Error: %s: when declare a struct, the field %s is redeclared; its first occurrence is %s"
                            (meta_str f1) f1.data (meta_str f2))
     | KindMismatch1 (x, m, t) ->
        die (fun p -> p.fmt "Error: %s: %s is used as a variable but was bound as a type in %s"
                            (meta_str x) x.data (meta_str m))
     | KindMismatch2 (x, t, t') ->
        die (fun p -> p.fmt "Error: %s: %s is used as a type but is defined as a definition in %s"
                            (meta_str x) x.data (meta_str t))
     | AssignToConst (x, y, t) ->
        die (fun p -> p.fmt "Error: %s: %s is a constant defined in %s but is being assigned to"
                            (meta_str x) x.data (meta_str y))
     | TypeNotDefined x ->
        die (fun p -> p.fmt "Error: %s: %s is used as a type but is not defined" (meta_str x) x.data)
     | TypeMismatch (e, ts) ->
        die (fun p -> p.fmt "Error: %s: the expression %s has type %s, but the following type(s) is(are) expected: %s"
                            (emeta_str e) (texpr_pprint e)
                            (etyp_pprint e) (comma_concat Typed.typ_pprint ts))
     | ResolvedTypeMismatch (e, ts) ->
        die (fun p -> p.fmt "Error: %s: the expression %s has type %s, but the following resolved type(s) is(are) expected: %s"
                            (emeta_str e) (expr_pprint_paren (to_untyped_expr e))
                            (etyp_pprint e) (comma_concat Typed.typ_pprint ts))
     | NotComparable e ->
        die (fun p -> p.fmt "Error: %s: the expression %s has type %s which is not comparable"
                            (emeta_str e) (texpr_pprint e) (Typed.typ_pprint (get_typ e)))
     | FieldNotFound (e, f) ->
        begin match get_typ e with
        | Tstruct _ ->
           die (fun p -> p.fmt "Error: %s: the expression %s resolves to a struct type which does not have the field %s"
                               (emeta_str e) (texpr_pprint e) f)
        | _ ->
           die (fun p -> p.fmt "Error: %s: the expression %s does not resolve to a struct type to access the field %s"
                               (emeta_str e) (texpr_pprint e) f)
        end
     | ExpectArrOrSlice e ->
        die (fun p -> p.fmt "Error: %s: the expression %s is expected to be an array or a slice but is a %s"
                            (emeta_str e) (texpr_pprint e) (etyp_pprint e))
     | ExpectSlice e ->
        die (fun p -> p.fmt "Error: %s: the expression %s is expected to be a slice but is a %s"
                            (emeta_str e) (texpr_pprint e) (etyp_pprint e))
     | InvalidLHS e -> 
        die (fun p -> p.fmt "Error: %s: %s is an invalid LHS expression" (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
     | ExpectFunc e ->
        die (fun p -> p.fmt "Error: %s: the expression %s is expected to be a function but is a %s"
                            (emeta_str e) (texpr_pprint e) (etyp_pprint e))
     | ParamTooFew (e, ts) ->
        die (fun p -> p.fmt "Error: %s: the application %s is expected to have %d more parameter(s) of the following types: %s"
                            (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e)
                            (List.length ts) (comma_concat Typed.typ_pprint ts))
     | ParamTooMany (e, ts) ->
        die (fun p -> p.fmt "Error: %s: the application has too many parameters: %s"
                            (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
     | CastParamMustOne (e, t) ->
        die (fun p -> p.fmt "Error: %s: the type cast %s must take 1 parameter"
                            (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
     | CastError (t, e) ->
        die (fun p -> p.fmt "Error: %s: the expression %s has type %s which cannot be cast to %s"
                            (emeta_str e) (texpr_pprint e) (etyp_pprint e) t)

     | IntParseError s ->       (* impossible *)
        die (fun p -> p.fmt "Error: %s: the integer representation %s is not well formated" (meta_str s) s.data)
     | IntParseOverflow s ->
        die (fun p -> p.fmt "Error: %s: the integer representation %s cannot be fit in 32 bits" (meta_str s) s.data)

     | VDeclNumMismatch (ns, es) ->
        let rec iter ns es =
          match ns, es with
          | [], []           -> raise Impossible
          | n :: _, []       ->
             die (fun p -> p.fmt "Error: %s: the name %s is not assigned an expression" (meta_str n) (name_str n.data))
          | [], e :: _       ->
             die (fun p -> p.fmt "Error: %s: the expression %s is not received by a name"
                                 (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
          | n :: ns, e :: es -> iter ns es in
        iter ns es
     | Redecl (x, k, m) ->
        begin match k with
        | Gbnd _
          | Lbnd _ ->
           die (fun p -> p.fmt "Error: %s: %s defined in %s is redeclared in the same scope as a variable"
                               (meta_str x) x.data (meta_str m))
        | Alias _
          | Tbnd _ ->
           die (fun p -> p.fmt "Error: %s: %s defined in %s is redeclared in the same scope as a type"
                               (meta_str x) x.data (meta_str m))
        | BConst _ ->           (* impossible *)
           die (fun p -> p.fmt "Error: %s: %s defined in %s is redeclared in the same scope as a boolean constant"
                               (meta_str x) x.data (meta_str m))
        | Func t   ->
           die (fun p -> p.fmt "Error: %s: %s defined in %s is redeclared in the same scope as a function"
                               (meta_str x) x.data (meta_str m))
        end
     | MissingType m ->         (* impossible *)
        die (fun p -> p.fmt "Error: %s: a declaration with no expression should come with a type" (meta_str m))
     | NumOfSidesMismatch (es1, es2) ->
        let rec iter es1 es2 =
          match es1, es2 with
          | [], []             -> raise Impossible
          | e :: _, []         ->
             die (fun p -> p.fmt "Error: %s: the expression %s is not assigned to"
                                 (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
          | [], e :: _         ->
             die (fun p -> p.fmt "Error: %s: the expression %s is not received by another expression"
                                 (meta_str (Untyped.expr_meta e)) (expr_pprint_paren e))
          | _ :: es1, _ :: es2 -> iter es1 es2 in
        iter es1 es2
     | RedeclInShortDecl (x, y) ->
        die (fun p -> p.fmt "Error: %s: %s is declared a second time in %s" (meta_str x) x.data (meta_str y))
     | NewVarInShortDecl (m, ns) ->
        die (fun p -> p.fmt "Error: %s: the follow names in the short declaration has no new names: %s"
                            (meta_str m) (comma_concat (fun n -> name_str n.data) ns))
     | UnassignableType e ->
        die (fun p -> p.fmt "Error: %s: the expression %s has unassignable type: %s"
                            (meta_str (expr_meta e)) (texpr_pprint e) (etyp_pprint e))
     | AssignOpTypeMismatch (m, t1, t2) -> (* this is probably not possible too *)
        die (fun p -> p.fmt "Error: %s: the lhs of the assignment with an operator has type %s but gives %s per the operator"
                            (meta_str m) (Typed.typ_pprint t1) (Typed.typ_pprint t2))
     | SpecialFuncWrongType m ->
        die (fun p -> p.fmt "Error: %s: the %s function must have type func()" (meta_str m) m.data)
     | ReturnTypeMismatch (m, t1, t2) -> 
        die (fun p -> p.fmt "Error: %s: return statement is expected to have type %s but it has type %s"
         (meta_str m) (Typed.typ_pprint t1) (Typed.typ_pprint t2))
     | MissingTermStmt (m, t1) ->
        die (fun p -> p.fmt "Error: %s: function %s has type %s but does not always end with a return statement"
         (meta_str m) (name_str m.data) (Typed.typ_pprint t1))
     | InvalidRecursiveType (f, t) ->
        die (fun p -> p.fmt "Error: %s: the field %s has an invalid recursive reference when defining a type in %s"
                            (meta_str f) f.data (meta_str (Untyped.typ_meta t)))

let cg_catch_exn f =
  try
    f ()
  with TcInconsistency (m, s) ->
        die (fun p -> p.fmt "Error: %s: %s" (meta_str m) s)
     | BrokenFunction s ->
        die (fun p -> p.fmt "Error: %s: codegen for function %s is broken" (meta_str s) s.data)
     | BrokenModule (s, m) ->
        die (fun p -> p.fmt "Error: %s" s;
            p.fmt "%s" m)
     | CgGlobalVarNotFound s
       | CgLocalVarNotFound (s, _) ->
        die (fun p -> p.fmt "Error: %s: during codegen, location of variable %s is not found" (meta_str s) s.data)

let compose f g h = f (fun () -> g h)
        
let scan ch =
  let f () =
    let lexbuf = Lexing.from_channel ch in
    let supp   = I.go_lexbuf_to_supplier read lexbuf in
    try
      while true do
        let (tkn, _, _) = supp () in
        match tkn with
        | EOF _ -> raise Break
        | _ -> ()
      done
    with Break -> () in
  lexer_catch_exn f

let tokens ch =
  let f () =
    let lexbuf = Lexing.from_channel ch in
    let supp   = I.go_lexbuf_to_supplier read lexbuf in
    try
      while true do
        let (tkn, _, _) = supp () in
        match tkn with
        | EOF _ -> raise Break
        | _ -> print_endline (tokenizer tkn)
      done
    with Break ->
      exit 0 in
  lexer_catch_exn f

let do_parse ch =
  let lexbuf = Lexing.from_channel ch in
  compose parser_catch_exn lexer_catch_exn
          (fun () -> Untyped.remove_paren (Untyped.check_continue_break (parse_loop lexbuf (I.program lexbuf.lex_curr_p))))

let parse ch = let _ = do_parse ch in ()

let pretty ch =
  let prog = do_parse ch in
  List.iter print_endline (program_pprint prog)

let do_type_check ch =
  let prog = do_parse ch in tc_catch_exn (fun () -> tc_program prog)

let type_check ch = let _ = do_type_check ch in ()

let print_kind indent n (k : kind) =
  match k, n with
  | (Gbnd t
     | Lbnd (_, t)), X x ->
     print_endline (sprintf "%s%s [variable] = %s" indent x (Typed.typ_pprint t))
  | Func t, Blank        ->
     print_endline (sprintf "%s%s [function] = <unmapped>" indent "_")
  | Func t, X x         ->
     print_endline (sprintf "%s%s [function] = %s" indent x (if x = "init" then "<unmapped>" else Typed.typ_pprint t))
  | BConst _, X x       ->
     print_endline (sprintf "%s%s [constant] = %s" indent x (Typed.typ_pprint Tbool))
  | Tbnd t, X x          ->
     print_endline (sprintf "%s%s [type] = %s (resolved to %s)" indent x x (Typed.typ_pprint t))
  | Alias t, X x         ->
     print_endline (sprintf "%s%s [type] = %s" indent x (Typed.typ_pprint t))
  | _ , Blank            -> ()

let print_local_bnd vl indent i =
  let x, t = List.nth vl i in
  print_kind indent (X x) (Lbnd (i, t))
                          
let symbol_simp_stmt vl indent s =
  match s with
  | ShortDecl (_, nes) ->
     List.iter (function
                | {data = New x}, e -> print_local_bnd vl indent x
                | _                 -> ())
               nes
  | _                  -> ()

let symbol_gdecl indent (d : gdecl) =
  match d with
  | VarDecl1 (_, nes)    ->
     List.iter (function
                | {data = X x}, e -> print_kind indent (X x) (Gbnd (get_typ e))
                | _               -> ())
               nes
  | VarDecl2 (_, ns, t)  ->
     List.iter (function
                | {data = X x} -> print_kind indent (X x) (Gbnd t)
                | _            -> ())
               ns
  | VarDecl3 (_, nes, t) ->
     List.iter (function
                | {data = X x}, _ -> print_kind indent (X x) (Gbnd t)
                | _               -> ())
               nes
  | TypDecl (_, n, t)    ->
     print_kind indent (X n.data) (Tbnd t)

let symbol_ldecl vl indent (d : ldecl) =
  match d with
  | VarDecl1 (_, nes)    ->
     List.iter (function
                | {data = X x}, e -> print_local_bnd vl indent x
                | _               -> ())
               nes
  | VarDecl2 (_, ns, t)  ->
     List.iter (function
                | {data = X x} -> print_local_bnd vl indent x
                | _            -> ())
               ns
  | VarDecl3 (_, nes, t) ->
     List.iter (function
                | {data = X x}, _ -> print_local_bnd vl indent x
                | _               -> ())
               nes
  | TypDecl (_, n, t)    ->
     print_kind indent (X n.data) (Tbnd t)

let rec symbol_stmt vl indent (s : stmt) =
  match s with
  | Simpl s                   -> symbol_simp_stmt vl indent s     
  | Decl d                    -> symbol_ldecl vl indent d
  | Block ss                  ->
     print_endline (indent ^ "{");
     symbol_stmts vl (indent_level ^ indent) ss;
     print_endline (indent ^ "}")
  | Print _                   -> ()
  | Println _                 -> ()
  | Return _                  -> ()
  | If (_, s, _, ifs, els)    ->
     print_endline (indent ^ "{");
     let indent' = indent_level ^ indent in
     symbol_simp_stmt vl indent' s;
     print_endline (indent' ^ "{");
     symbol_stmts vl (indent_level ^ indent') ifs;
     print_endline (indent' ^ "}");
     Option.iter (fun el ->
         print_endline (indent' ^ "{");
         symbol_stmts vl (indent_level ^ indent') el;
         print_endline (indent' ^ "}")
       ) els;
     print_endline (indent ^ "}")
  | Switch (_, s, _, cs, dfl) ->
     print_endline (indent ^ "{");
     let indent' = indent_level ^ indent in
     symbol_simp_stmt vl indent' s;
     List.iter (fun c -> 
         print_endline (indent' ^ "{");
         symbol_stmt_list vl (indent_level ^ indent') c.exec;
         print_endline (indent' ^ "}")
       ) cs;
     Option.iter (fun df ->
         print_endline (indent' ^ "{");
         symbol_stmt_list vl (indent_level ^ indent') df;
         print_endline (indent' ^ "}")
       ) dfl;
     print_endline (indent ^ "}")
  | For (_, s, _, _, ss)      ->
     print_endline (indent ^ "{");
     let indent' = indent_level ^ indent in
     symbol_simp_stmt vl indent' s;
     print_endline (indent' ^ "{");
     symbol_stmts vl (indent_level ^ indent') ss;
     print_endline (indent' ^ "}");
     print_endline (indent ^ "}")
  | Break _                   -> ()
  | Continue _                -> ()

and symbol_stmt_list vl indent (ss : stmt list) =
  List.iter (symbol_stmt vl indent) ss

and symbol_stmts vl indent (ss : stmts) =
  symbol_stmt_list vl indent ss.data

let symbol_top_decl indent (d : top_decl) =
  match d with
  | DDecl d                       -> symbol_gdecl indent d
  | FunDecl (_, f, ns, t, vl, ss) ->
     print_kind indent f.data (Func (Tfun (List.map snd ns, t)));
     print_endline (indent ^ "{");
     let indent' = indent_level ^ indent in
     List.iter (fun (n, t) ->
         match n.data with
         | Blank -> ()
         | X i   -> print_local_bnd vl indent' i
       ) ns;
     symbol_stmts vl indent' ss;
     print_endline (indent ^ "}")

let symbol_program (p : program) =
  print_endline "{";
  print_endline (indent_level ^ "int [type] = int");
  print_endline (indent_level ^ "float64 [type] = float64");
  print_endline (indent_level ^ "bool [type] = bool");
  print_endline (indent_level ^ "rune [type] = rune");
  print_endline (indent_level ^ "string [type] = string");
  print_endline (indent_level ^ "true [constant] = bool");
  print_endline (indent_level ^ "false [constant] = bool");
  print_endline (indent_level ^ "{");
  List.iter (symbol_top_decl (indent_level ^ indent_level)) p.top_decls;
  print_endline (indent_level ^ "}");
  print_endline "}"

let symbol ch =
  let _, prog = do_type_check ch in
  symbol_program prog

let run_with_file worker file =
  match file with
  | None ->
     worker stdin file
  | Some f ->
     try
       let inh = open_in f in
       try
         worker inh file;
         close_in inh
       with e ->
         close_in inh;
         raise e
     with Sys_error s ->
           prerr_endline ("Error: " ^ s);
           exit 1
        | _ ->
           prerr_endline "Error: unknown error";
           exit 1

let run worker file =
  run_with_file (fun h _ -> worker h) file

let codegen ch f =
  let _, prog = do_type_check ch in
  let g = cg_catch_exn (fun () -> codegen_program prog) in
  let m = string_of_llmodule g.cgmod in
  match f with
  | None -> print_endline m
  | Some f ->
     let fo = (Filename.remove_extension f) ^ ".ll" in
     Core.Out_channel.write_all fo ~data:m;
     exit_ok ()

let () =
  let l = Array.length Sys.argv in
  if l > 1 && l <= 3 then
    let mode = Sys.argv.(1)
    and file = if Array.length Sys.argv = 3 then Some Sys.argv.(2) else None in
    match mode with
    | "scan"      ->
        run scan file;
        exit_ok ()
    | "token"     ->
       run tokens file
    | "parse"     ->
        run parse file;
        exit_ok ()
    | "pretty"    ->
       run pretty file
    | "typecheck" ->
       run type_check file;
       exit_ok ()
    | "symbol"    ->
       run symbol file
    | "codegen"    ->
       run_with_file codegen file
    | _           ->
      prerr_endline help_message;
        exit 1
  else
    begin
      prerr_endline help_message;
      exit 1
    end

