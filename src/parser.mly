%{
    open Meta
    open Ast
    open Tags
    open Common
    open Parser_exn
                                  
    type incr_decr =
      | Inc | Dec

    let ident_to_name x = update_data x (X x.data)

    let blank_to_name x = update_data x Blank

    let true_val m = Bool (update_data m True)
                   
    let rec exprs_to_names es =
      match es with
      | []          -> []
      | Var x :: es -> x :: exprs_to_names es
      | e :: _      -> raise (ShortDeclIdents e)

    type switch =
      | Default of unit meta
      | Case of expr list

    let validate_cases cs =
      let rec helper cs rcs df =
        match cs with
        | []                    -> List.rev rcs, df
        | (Case es, ss) :: cs   -> helper cs ({ cond = es ; exec = ss } :: rcs) df
        | (Default m, ss) :: cs ->
           match df with
           | None   -> helper cs rcs (Some ss)
           | Some _ -> raise (AtMostOneDefault m)
      in
      helper cs [] None

    let update_nop_loc s m =
      match s with
      | Nop _ -> Nop m
      | _     -> s

    let vdecl_meta ids s =
      let x = List.hd ids in
      range x s ()
%}

%token PACKAGE
%token ASSIGN 
%token SHORTASSIGN PLUSASSIGN TIMESASSIGN MINUSASSIGN DIVASSIGN MODULEASSIGN 
%token BITANDASSIGN BITORASSIGN BITXORASSIGN BINLEFTSHIFTASSIGN BINRIGHTSHIFTASSIGN BITCLRASSIGN
%token COLON
%token COMMA
%token<unit Meta.meta> SEMI
%token<unit Meta.meta> SEMINL
%token<unit Meta.meta> VAR IF CASE DEFAULTCASE
%token<unit Meta.meta> FORLO SWITCH
%token ELSE
%token<unit Meta.meta> BREAK CONTINUE
%token<unit Meta.meta> LPAREN LSQBRACKET LCBRACKET RPAREN RSQBRACKET RCBRACKET

%token<unit Meta.meta> PRINT PRINTLN APPEND LEN CAP
%token<unit Meta.meta> EOF

// others

%token<string Meta.meta> IDENT
%token<Tags.int_kind * string Meta.meta> INTVAL
%token<Tags.float_kind * string Meta.meta> FVAL
%token<string * char Meta.meta> RUNEVAL
/* the first string is the original string representation. the second one is the interpreted one. */
%token<Tags.str_kind * string * string Meta.meta> SVAL
%token<unit Meta.meta> BLANKIDENT

// operators
%token TIMES DIV MODULE
%token<unit Meta.meta> PLUS MINUS

// comparisons
%token EQ NEQ GE LE GT LT
// logic operators
%token AND OR
%token<unit Meta.meta> NOT

//bitwise
%token BITAND BITOR CHANNELOP
%token BINLEFTSHIFT BINRIGHTSHIFT
%token BITCLR
%token<unit Meta.meta> XOR

%token<unit Meta.meta> INCR DECR

%token<unit Meta.meta> TYPEKEY FUNC RETURN STRUCT
%token SELECTOR
%token GOSTMT
%token GOTOSTMT
%token FALLTHROUGH
%token VARIADIC
%token INTERFACE
%token SELECT
%token DEFER
%token MAP
%token CHANNEL
%token CONST
%token RANGE
%token IMPORT


%left OR
%left AND
%left EQ NEQ GE LE GT LT
%left PLUS MINUS BITOR XOR
%left TIMES DIV MODULE BINLEFTSHIFT BINRIGHTSHIFT BITCLR BITAND
// %nonassoc NOT

%start program
%type <Ast.program> program

%%
program: 
  | PACKAGE i = IDENT semieof tds = top_level_decl* EOF
    { { pkg_decl = i ; top_decls = tds } }

top_level_decl:  
  | d = decl          { DDecl d }
  | d = function_decl { d }

expr: 
  | e = unary_expr { e }
  | e1 = expr bo = binop e2 = expr { new_binop bo e1 e2 }

unary_expr:
  | u = primary_expr { u }
  | uo = unop ue = unary_expr { new_uniop uo ue }

%inline binop:
  | OR    { Lo Or }
  | AND   { Lo And }
  | op = relop { Lo op }
  | op = addop { Ar op }
  | op = mulop { Ar op}

%inline relop:
  | EQ  { Eq }
  | NEQ { Neq }
  | GE  { Ge }
  | GT  { Gt }
  | LE  { Le }
  | LT  { Lt }

%inline addop:
  | PLUS  { Plus }
  | MINUS { Minus }
  | BITOR { Bor }
  | XOR   { Bxor }

%inline mulop:
  | TIMES         { Times }
  | DIV           { Div }
  | MODULE        { Rem }
  | BINLEFTSHIFT  { Lshift }
  | BINRIGHTSHIFT { Rshift }
  | BITAND        { Band }
  | BITCLR        { Bclear }

unop:
  | x = PLUS  { update_data x Pos }
  | x = MINUS { update_data x Neg }
  | x = NOT   { update_data x Not }
  | x = XOR   { update_data x Bcomp }
//| TIMES {  }
//| BITAND {  }
//| CHANNELOP {  }

primary_expr: 
  | pe = operand { pe }
  | pe = primary_expr s = selector { new_selector pe s }
  | pe = primary_expr i = index { let e2, rs = i in new_idx pe e2 rs }
  | pe = primary_expr a = arguments { let es, r = a in new_app pe es r }
  | t = APPEND LPAREN e1 = expr COMMA e2 = expr c = RPAREN { Append (range t c (), e1, e2) }
  | t = CAP LPAREN e = expr c = RPAREN { Cap (range t c (), e) }
  | t = LEN LPAREN e = expr c = RPAREN { Len (range t c (), e) }
//  | pe = primary_expr slice {  }
//  | pe = primary_expr type_assertion {  }
//  | pe = conversion {  }

operand: 
  | l = literal            { l }
  | x = operand_name       { Var x }
  | LPAREN e = expr RPAREN { Paren e }

%inline literal: 
  | l = basic_lit { l }
//  | l = composite_lit {  }
//  | l = function_lit {  }

basic_lit:
  | i = INTVAL  { let (k, i) = i in Int (k, i) }
  | f = FVAL    { let (k, f) = f in Float (k, f)  }
  | c = RUNEVAL { let (s, c) = c in Rune (s, c) }
  | s = SVAL    { let (k, s1, s2) = s in String (k, s1, s2) }

operand_name: 
  | x = IDENT      { ident_to_name x }
  | x = BLANKIDENT { blank_to_name x }

%inline selector:
  | SELECTOR i = IDENT { i }

%inline index:
  | LSQBRACKET e = expr rs = RSQBRACKET { e, rs }

%inline arguments:
  | LPAREN es = expr_list_opt r = RPAREN { es, r }
//| a = LPAREN expr_list COMMA RPAREN {  }
//| a = LPAREN expr_list VARIADIC COMMA RPAREN {  }
//| a = LPAREN expr_list VARIADIC RPAREN {  }
//| a = LPAREN gotype COMMA expr_list VARIADIC COMMA RPAREN {  }
//| a = LPAREN gotype COMMA expr_list COMMA RPAREN {  }
//| a = LPAREN gotype COMMA expr_list VARIADIC RPAREN {  }

gotype: 
  | t = type_name            { Tref t }
  | t = type_lit             { t }
  | LPAREN t = gotype RPAREN { t }

// we do not support interface_type
type_lit:
  | a = array_type     { a }
  | s = struct_type    { s }   
  | s = slice_type     { s }   
//| tl = pointer_type  {  }     
//| tl = function_type {  }     
//| tl = map_type      {  }     
//| tl = channel_type  {  }

%inline struct_type:
  | st = STRUCT LCBRACKET fs = list(f = field_decl semi { f }) cb = RCBRACKET { Tstruct (range st cb (), fs) }

%inline field_decl:
  | ids = identifier_list t = gotype { ids, t }
//| t = embedded_field               { [], t }
//| id = identifier_list gotype tag  {  }         
//| id = embedded_field tag          {  }       

%inline eleme_type: 
  | t = gotype { t }

%inline array_type: 
  | lb = LSQBRACKET l = array_length RSQBRACKET t = eleme_type { let (k, i) = l in Tarray (range lb (typ_meta t) (), k, i, t) }

%inline array_length:
  | l = INTVAL { l }

//%inline embedded_field:
//| tn = type_name { Tref tn }
//| ef = TIMES type_name {  }

// we do not support qualified identifiers
%inline type_name:
  | tn = IDENT { tn }

%inline slice_type:
  | lb = LSQBRACKET RSQBRACKET t = eleme_type { Tslice (range lb (typ_meta t) (), t) }

stmt: 
  | d = decl                                              { Decl d }
  | s = simple_stmt m = semi                              { Simpl (update_nop_loc s m) }
  | s = return_stmt                                       { s }
  | s = break_stmt                                        { s }
  | s = continue_stmt                                     { s }
  | b = block semi                                        { Block b }
  | s = if_stmt                                           { s }
  | s = switch_stmt                                       { s }
  | s = for_stmt                                          { s }
  | s = PRINT LPAREN es = expr_list_opt RPAREN m = semi   { Print (range s m es) }
  | s = PRINTLN LPAREN es = expr_list_opt RPAREN m = semi { Println (range s m es) }
//| s = labeled_stmt {}
//| s = defer_stmt {}
//| s = goto_stmt {}
//| s = fallthrough_stmt {}
//| s = select_stmt {}
//| s = go_stmt {}

simple_stmt:
  | { Nop meta_zero }
  | e = expr op = inc_dec_stmt_opt
    { match op with 
      | Some (p, Inc) -> Incr (update_data p e)
      | Some (p, Dec) -> Decr (update_data p e)
      | None          -> match e with
                         | App (m, f, es) -> FApp (m, f, es)
                         | _              -> raise (NotFuncApplication e) }
  | s = assign_stmt    { s }
  | s = short_var_decl { s }
//| send_stmt  {}

inc_dec_stmt_opt:  
  | { None }
  | p = INCR { Some (p, Inc) }
  | p = DECR { Some (p, Dec) }

semi:
  | s = SEMI   { s }
  | s = SEMINL { s }

semieof:
  | s = EOF    { s }
  | s = SEMI   { s }
  | s = SEMINL { s }

%inline expr_list_opt:
  | es = separated_list(COMMA, expr) { es }

%inline expr_list:
  | es = separated_nonempty_list(COMMA, expr) { es }

assign_stmt:
  | ls = expr_list ASSIGN rs = expr_list
    { (* ls and rs are surely non-empty because they are constructed as nonempty lists *)
      let l = List.hd ls
      and r = List.hd (List.rev rs) in
      Assign (range (expr_meta l) (expr_meta r) (), ls, rs)
    }
  | l = expr op = assign_op r = expr
    { (* ls and rs are surely non-empty because they are constructed as nonempty lists *)
      AssignOp (range (expr_meta l) (expr_meta r) (), l, op, r)
    }

%inline assign_op:
  | PLUSASSIGN          { Plus }
  | TIMESASSIGN         { Times }
  | MINUSASSIGN         { Minus }
  | DIVASSIGN           { Div }
  | MODULEASSIGN        { Rem }
  | BITANDASSIGN        { Band }
  | BITORASSIGN         { Bor }
  | BITXORASSIGN        { Bxor }
  | BINLEFTSHIFTASSIGN  { Lshift }
  | BINRIGHTSHIFTASSIGN { Rshift }
  | BITCLRASSIGN        { Bclear }

%inline short_var_decl: 
  | ls = expr_list SHORTASSIGN rs = expr_list
    { (* ls and rs are surely non-empty because they are constructed as nonempty lists *)
      let l = List.hd ls
      and r = List.hd (List.rev rs) in
      ShortDecl (range (expr_meta l) (expr_meta r) (), exprs_to_names ls, rs) }

%inline identifier_list:
  | ids = separated_nonempty_list(COMMA, operand_name) { ids }

decl: 
  | d = var_decl  { d }
  | d = type_decl { d }

var_decl:
  | v = VAR vspc = var_spec
    { let m, vs, t, es = vspc in VarDecl (range v m (), vs, t, es) }
  | v = VAR LPAREN vs=list(var_spec) cp = RPAREN semieof
    { VarDecls (range v cp vs) }

var_spec:
  | vs = identifier_list t = gotype s = semieof                       { (vdecl_meta vs s, vs, Some t, []) }
  | vs = identifier_list t = gotype ASSIGN es = expr_list s = semieof { (vdecl_meta vs s, vs, Some t, es) }
  | vs = identifier_list ASSIGN es = expr_list s = semieof            { (vdecl_meta vs s, vs, None, es) }


type_decl:  
  | td = TYPEKEY spc = type_spec
    { let (m, i, t) = spc in TypDecl (range td m (), i, t) }
  | td = TYPEKEY LPAREN ts = list(type_spec) cp = RPAREN semieof
    { TypDecls (range td cp ts) }

%inline type_spec:
  | ts = type_def { ts }
//| ts = alias_decl {}

%inline type_def:
  | i = operand_name t = gotype s = semieof { (range i s (), i, t) }

return_stmt: 
  | r = RETURN e = expr s = semi { Return (range r s (Some e)) }
  | r = RETURN s = semi          { Return (range r s None) }

%inline break_stmt: 
  | b = BREAK s = semi { Break (range b s ()) }
//| BREAK label {}

%inline continue_stmt:
  | c = CONTINUE s = semi { Continue (range c s ()) } 
//| CONTINUE label {}

%inline block: 
  | o = LCBRACKET ss = statements_list c = RCBRACKET { range o c ss }

%inline statements_list:
  | ss = stmt* { ss }

if_stmt:
  | i = IF s = simple_stmt m = semi e = expr ss1 = block ELSE ss2 = if_stmt
    { If (range i (stmt_meta ss2) (), update_nop_loc s m, e, ss1, Some (update_data (stmt_meta ss2) [ss2])) } 
  | i = IF s = simple_stmt m = semi e = expr ss1 = block ELSE ss2 = block semi
    { If (range i (stmts_meta ss2) (), update_nop_loc s m, e, ss1, Some ss2) }
  | i = IF e = expr ss1 = block ELSE ss2 = if_stmt
    { If (range i (stmt_meta ss2) (), Nop i, e, ss1, Some (update_data (stmt_meta ss2) [ss2])) }
  | i = IF e = expr ss1 = block ELSE ss2 = block semi
    { If (range i (stmts_meta ss2) (), Nop i, e, ss1, Some ss2) }
  | i = IF s = simple_stmt m = semi e = expr ss = block semi
    { If (range i (stmts_meta ss) (), update_nop_loc s m, e, ss, None) }
  | i = IF e = expr ss = block semi
    { If (range i (stmts_meta ss) (), Nop i, e, ss, None) }

for_stmt:
  | f = FORLO c = condition b = block semi
    { For (range f (stmts_meta b) (), Nop f, Some c, Nop f, b) }
  | f = FORLO c = for_clause b = block semi
    { let s1, e, s2 = c in
      For (range f (stmts_meta b) (), s1, e, s2, b) }
  | f = FORLO b = block semi
    { For (range f (stmts_meta b) (), Nop f, None, Nop f, b) }
//| FORLO range_clause block {}

%inline condition:
  | e = expr { e }

for_clause:
  | s1 = init_stmt e = condition m = semi s2 = post_stmt { s1, Some e, update_nop_loc s2 m }
  | s1 = init_stmt m = semi s2 = post_stmt               { s1, None, update_nop_loc s2 m }

%inline init_stmt:
  | s = simple_stmt m = semi { update_nop_loc s m }

%inline post_stmt:
  | s = simple_stmt
    { match s with
      | ShortDecl _ -> raise (ForPostNoShortDecl s)
      | _           -> s }

%inline switch_stmt:
  | s = expr_swtich_stmt semi { s }
//| type_switch_stmt {}

expr_swtich_stmt:
  | sw = SWITCH s = simple_stmt semi e = expr LCBRACKET cs = expr_case_clause* cb = RCBRACKET
    { let (cl, df) = validate_cases cs in
      Switch (range sw cb (), s, e, cl, df) }
  | sw = SWITCH e = expr LCBRACKET cs = expr_case_clause* cb = RCBRACKET
    { let (cl, df) = validate_cases cs in
      Switch (range sw cb (), Nop sw, e, cl, df) }
  | sw = SWITCH s = simple_stmt m = semi LCBRACKET cs = expr_case_clause* cb = RCBRACKET
    { let (cl, df) = validate_cases cs in
      Switch (range sw cb (), s, true_val m, cl, df) }
  | sw = SWITCH l = LCBRACKET cs = expr_case_clause* cb = RCBRACKET
    { let (cl, df) = validate_cases cs in
      Switch (range sw cb (), Nop sw, true_val l, cl, df) }

%inline expr_case_clause:
  | c = expr_switch_case COLON ss = statements_list { (c, ss) }

expr_switch_case:
  | CASE es = expr_list { Case es }
  | m = DEFAULTCASE     { Default m }

function_decl:
  | f = FUNC n = function_name sg = signature ob = LCBRACKET ss = statements_list cb = RCBRACKET semieof
    { let s, t = sg in FunDecl (range f cb (), n, s, t, range ob cb ss) }
//| FUNC function_name signature {}

%inline function_name:
  | n = operand_name { n }

%inline signature: 
  | s = parameters t = gotype? { s, t }

%inline parameters:
  | LPAREN ps = params_list RPAREN { ps }

%inline params_list: 
  | ps = separated_list(COMMA, param_decl) { ps }

%inline param_decl:
  | ids = identifier_list t = gotype { ids, t }


/*

range_clause:
  | expr_list ASSIGN RANGE expr {}
  | identifier_list SHORTASSIGN RANGE expr {}








//alias_decl:
//  | ad = IDENT ASSIGN gotype {}






//composite_lit: 
// | cl = lit_type lit_val {  }

lit_type: 
  | lt = struct_type {  }           
  | lt = array_type  {  }             
  | lt = LSQBRACKET VARIADIC RSQBRACKET eleme_type {  } 
  | lt = slice_type  {  }           
  | lt = map_type    {  }               
  | lt = type_name   {  }

lit_val: 
  | lv = LCBRACKET eleme_list COMMA RCBRACKET {  }
  | lv = LCBRACKET eleme_list RCBRACKET {  }
  | lv = LCBRACKET COMMA RCBRACKET {  }
  | lv = LCBRACKET RCBRACKET {  }

eleme_list:  
  | el = keyed_eleme {  }
  | el = keyed_eleme COMMA keyed_eleme {  }

keyed_eleme:
  | ke = key COLON element {  }
  | ke = element {  }

key: 
  | k = field_name {  }
  | k = expr {  }
  | k = lit_val {  }

field_name:
  | fn = IDENT {  }

element: 
  | el = expr {  }
  | el = lit_val {  }

// see https://golang.org/ref/spec#string_lit, we might need to redefine this tag 
tag: 
  | t = SVAL {  }




pointer_type:
  | pt = TIMES gotype {  }

function_type: 
  | ft = FUNC signature {  }





map_type:
  | m = MAP LSQBRACKET key_type RSQBRACKET eleme_type { }

key_type:
  | kt = gotype {  }

channel_type: 
  | ct = CHANNEL eleme_type {  }
  | ct = CHANNEL CHANNELOP eleme_type {  }
  | ct = CHANNELOP CHANNEL eleme_type {  }




//function_lit:
//  | fl = FUNC signature func_body {  }



conversion:
  | c = gotype LPAREN expr RPAREN {  }
  | c = gotype LPAREN expr COMMA RPAREN {  }


slice:
  | s = LSQBRACKET expr COLON expr RSQBRACKET {  }
  | s = LSQBRACKET expr COLON RSQBRACKET {  }
  | s = LSQBRACKET expr COLON RSQBRACKET {  }
  | s = LSQBRACKET COLON expr COLON expr RSQBRACKET {  }
  | s = LSQBRACKET expr COLON expr COLON expr RSQBRACKET {  }

type_assertion:
  | s = SELECTOR LPAREN gotype RPAREN {  }










labeled_stmt:
  | label COLON stmt {}

label:
  | IDENT {}




send_stmt:
  | expr CHANNELOP expr {}




go_stmt: 
  | GOSTMT expr {}



goto_stmt:
  | GOTOSTMT label {}

fallthrough_stmt:
  | FALLTHROUGH {}



type_switch_stmt:
  | SWITCH simple_stmt SEMI type_switch_guard LCBRACKET type_case_clause* RCBRACKET {}
  | SWITCH type_switch_guard LCBRACKET type_case_clause* RCBRACKET {}

type_switch_guard:
  | IDENT SHORTASSIGN primary_expr SELECTOR LPAREN TYPEKEY RPAREN {} 
  | primary_expr SELECTOR LPAREN TYPEKEY RPAREN {} 

type_case_clause:  
  | type_switch_case COLON statements_list {}

type_switch_case:
  | CASE type_list {}
  | DEFAULTCASE {}

type_list:
  | gotype {}
  | gotype COMMA type_list {}

select_stmt:
  | SELECT LCBRACKET comm_clause RCBRACKET {}

comm_clause:
  | comm_case COLON statements_list {}

comm_case:
  | CASE send_stmt {}
  | CASE recv_stmt {}
  | DEFAULTCASE {}

recv_stmt:
  | expr_list ASSIGN recv_expr {}
  | identifier_list SHORTASSIGN recv_expr {}
  | recv_expr {}

recv_expr:
  | expr {}


defer_stmt:
  | DEFER expr {}



*/

