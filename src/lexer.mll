{
  open Meta
  open Lexing
  open Parser
  open Tags

  exception LexerError of string meta

  (* exceptions for general comments *)
  exception UnfinishedComment of unit meta
  
  (* shared exceptions of runes and strings *)
  exception NonAsciiChar of char meta
  exception UninterpretableEscape of string meta

  (* exceptions for rune parsing *)
  exception TooManyForRune of string meta
  exception TooFewForRune of unit meta
  exception UnfinishedRune of unit meta

  (* exceptions for string parsing *)
  exception UnfinishedString of str_kind * unit meta
  exception NewLineInInterpreted of unit meta
  
  let insert_semicolon t =
    match t with
    | IDENT _ 
      | BLANKIDENT _
      | INTVAL _
      | FVAL _
      | SVAL _
      | RUNEVAL _
      | BREAK _
      | CONTINUE _
      | FALLTHROUGH
      | RETURN _
      | INCR _ | DECR _
      | RPAREN _ | RSQBRACKET _ | RCBRACKET _ -> true
    | _ -> false

  let rune_lit lexbuf c =
    offset_start_c (coordinates lexbuf c) (-1) (* -1 because we want to count the opening single quote *)
  
}

let newline = '\n' | "\r\n"
let white   = [' ' '\t']+
let comment = "//" [^ '\n']*

let digit   = ['0'-'9']
let digit1  = ['0' '1']
let digit7  = ['0'-'7']
let digit9  = ['1'-'9']
let hexd    = digit | ['a'-'f' 'A'-'F']

(* integer literals *)
let decdigits = digit ('_' ? digit)*
let bindigits = digit1 ('_' ? digit1)*
let octdigits = digit7 ('_' ? digit7)*
let hexdigits = hexd ('_' ? hexd)*

let decint = "0" | digit9 ('_'? decdigits)?
let binint = '0' ('b' | 'B') '_'? bindigits
let octint = '0' ('o' | 'O')? '_'? octdigits
let hexint = '0' ('x' | 'X') '_'? hexdigits
let integer = decint | binint | octint | hexint

(* floating-point literals *)
let decexpo  = ('e' | 'E') ('+' | '-')? decdigits
let decfloat = decdigits '.' decdigits? decexpo?
             | decdigits decexpo
             | '.' decdigits decexpo?

let hexexpo = ('p' | 'P') ('+' | '-')? decdigits
let mantissa = '_'? hexdigits '.' hexdigits? | '_'? hexdigits | '.' hexdigits
let hexfloat = '0' ('x' | 'X') mantissa hexexpo

let float =  decfloat | hexfloat

(* identifiers *)
let letter = ['a'-'z' 'A'-'Z' '_']
let ident = letter (letter | digit)*


rule read prev = parse
          | white { read prev lexbuf }
            | newline { Lexing.new_line lexbuf;
                        match prev with
                        | None   -> read prev lexbuf
                        | Some t -> if insert_semicolon t then SEMINL (end_coord_meta lexbuf)
                                    else read prev lexbuf }

          (** comments

              see also: https://golang.org/ref/spec#Comments
           *)
          | comment { read prev lexbuf }
          | "/*" { if read_general_comment false lexbuf
                   then match prev with
                        | None   -> read prev lexbuf
                        | Some t -> if insert_semicolon t then SEMINL (end_coord_meta lexbuf)
                                    else read prev lexbuf
                   else read prev lexbuf }


          (** integers

              see also: https://golang.org/ref/spec#Integer_literals
           *)
          | decint as n { INTVAL (IDec, coordinates lexbuf n) }
          | binint as n { INTVAL (IBin, coordinates lexbuf n) }
          | octint as n { INTVAL (IOct, coordinates lexbuf n) }
          | hexint as n { INTVAL (IHex, coordinates lexbuf n) }

          (** floats

              see also: https://golang.org/ref/spec#Floating-point_literals
           *)
          | decfloat as f { FVAL (FDec, coordinates lexbuf f) }
          | hexfloat as f { FVAL (FHex, coordinates lexbuf f) }

          (** runes

              see also: https://golang.org/ref/spec#Rune_literals
           *)
          | '\'' { let (s, c) = read_rune lexbuf in RUNEVAL (s, c) }

          (** strings

              see also: https://golang.org/ref/spec#String_literals
           *)
          | '`' { let (sl, sc) = start_coord lexbuf
                  and buf_inp  = Buffer.create 10
                  and buf      = Buffer.create 10 in
                  Buffer.add_char buf_inp '`';
                  let (el, ec) = read_raw_string buf_inp buf lexbuf in
                  SVAL (Sraw, Buffer.contents buf_inp,
                        {
                          start_l = sl;
                          end_l   = el;
                          start_c = sc;
                          end_c   = ec;
                          data    = Buffer.contents buf
                        }) }
          | '"' { let (sl, sc) = start_coord lexbuf
                  and buf_inp  = Buffer.create 10
                  and buf      = Buffer.create 10 in
                  Buffer.add_char buf_inp '"';
                  let (el, ec) = read_interpreted_string buf_inp buf lexbuf in
                  SVAL (Sint, Buffer.contents buf_inp,
                        {
                          start_l = sl;
                          end_l   = el;
                          start_c = sc;
                          end_c   = ec;
                          data    = Buffer.contents buf
                        }) }

          (* other tokens *)
          | ';'   { SEMI (coordinates' lexbuf) }
          | ':'   { COLON }
          | ','   { COMMA }
          | '('   { LPAREN (coordinates' lexbuf) }
          | ')'   { RPAREN (coordinates' lexbuf) }
          | '['   { LSQBRACKET (coordinates' lexbuf) }
          | ']'   { RSQBRACKET (coordinates' lexbuf) }
          | '{'   { LCBRACKET (coordinates' lexbuf) }
          | '}'   { RCBRACKET (coordinates' lexbuf) }
          | '+'   { PLUS (coordinates' lexbuf) }
          | '-'   { MINUS (coordinates' lexbuf) }
          | '*'   { TIMES }
          | '/'   { DIV }
          | '%'   { MODULE }
          | '_'   { BLANKIDENT (coordinates' lexbuf) }
          | "="   { ASSIGN }
          | ":="  { SHORTASSIGN }
          | "+="  { PLUSASSIGN }
          | "*="  { TIMESASSIGN }
          | "-="  { MINUSASSIGN }
          | "/="  { DIVASSIGN }
          | "%="  { MODULEASSIGN }
          | "&="  { BITANDASSIGN }
          | "|="  { BITORASSIGN }
          | "^="  { BITXORASSIGN }
          | "<<="  { BINLEFTSHIFTASSIGN }
          | ">>="  { BINRIGHTSHIFTASSIGN }
          | "&^=" { BITCLRASSIGN }
          | "=="  { EQ }
          | "!="  { NEQ }
          | "!"   { NOT (coordinates' lexbuf) }
          | ">="  { GE }
          | ">"   { GT }
          | "<="  { LE }
          | "<"   { LT }
          | "&&"  { AND }
          | "||"  { OR }
          | "&"   { BITAND }
          | "|"   { BITOR }
          | "^"   { XOR (coordinates' lexbuf) }
          | "<<"  { BINLEFTSHIFT }
          | ">>"  { BINRIGHTSHIFT }
          | "&^"  { BITCLR }
          | "++"  { INCR (coordinates' lexbuf) }
          | "--"  { DECR (coordinates' lexbuf) }
          | "<-"  { CHANNELOP }
          | "..." { VARIADIC }
          | "."   { SELECTOR }
          | "if"  { IF (coordinates' lexbuf) }
          | "else" { ELSE }
          | "append" { APPEND (coordinates' lexbuf) }
          | "cap" { CAP (coordinates' lexbuf) }
          | "len" { LEN (coordinates' lexbuf) }
          | "switch" { SWITCH (coordinates' lexbuf) }
          | "case" { CASE (coordinates' lexbuf) }
          | "default" { DEFAULTCASE (coordinates' lexbuf) }
          | "continue" { CONTINUE (coordinates' lexbuf) }
          | "break" { BREAK (coordinates' lexbuf) }
          | "for" { FORLO (coordinates' lexbuf) }
          | "func"  { FUNC (coordinates' lexbuf) }
          | "interface" { INTERFACE }
          | "select" { SELECT }
          | "defer" { DEFER }
          | "map"  { MAP }
          | "struct" { STRUCT (coordinates' lexbuf) }
          | "go" { GOSTMT }
          | "goto" { GOTOSTMT }
          | "chan" { CHANNEL }
          | "package" { PACKAGE }
          | "const" { CONST }
          | "fallthrough" { FALLTHROUGH }
          | "range" { RANGE }
          | "type" { TYPEKEY (coordinates' lexbuf) }
          | "print" { PRINT (coordinates' lexbuf) }
          | "println" { PRINTLN (coordinates' lexbuf) }
          | "import" { IMPORT }
          | "return" { RETURN (coordinates' lexbuf) }
          | "var" { VAR (coordinates' lexbuf) }
          | ident as i { IDENT (coordinates lexbuf i) }
          | _ { raise (LexerError (coordinates lexbuf (Lexing.lexeme lexbuf))) }
          | eof { EOF (coordinates' lexbuf) }

(** we handle general comment here (comment block). *)
and read_general_comment nl =
  parse
| "*/" { nl }
| newline { Lexing.new_line lexbuf; read_general_comment true lexbuf }
| [ ^ '\r' '\n' ] { read_general_comment nl lexbuf }
| _ { raise (UnfinishedComment (coordinates' lexbuf)) }
| eof { raise (UnfinishedComment (coordinates' lexbuf)) }

(** we only handle escaped characters for rune.
    it returns a tuple (the program input, interpreted char in OCaml)
 *)
and read_rune =
  parse
| '\''           { raise (TooFewForRune (offset_start_c (coordinates' lexbuf) (-1))) }
| '\\' 'a' '\''  { "\'\\a\'", rune_lit lexbuf '\x07' }
| '\\' 'b' '\''  { "\'\\b\'" , rune_lit lexbuf '\x06' }
| '\\' 'f' '\''  { "\'\\f\'", rune_lit lexbuf '\x0c' }
| '\\' 'n' '\''  { "\'\\n\'", rune_lit lexbuf '\n' }
| '\\' 'r' '\''  { "\'\\r\'", rune_lit lexbuf '\r' }
| '\\' 't' '\''  { "\'\\t\'", rune_lit lexbuf '\t' }
| '\\' 'v' '\''  { "\'\\v\'", rune_lit lexbuf '\x0b' }
| '\\' '\\' '\'' { "\'\\\\\'", rune_lit lexbuf '\\' }
| '\\' '\'' '\'' { "\'\\'\'", rune_lit lexbuf '\'' }
| ('\\' _) as s  { raise (UninterpretableEscape (coordinates lexbuf s)) }
| [^ '\\' '\'' '\r' '\n'] as c '\'' { let cc = Char.code c in
                                      if cc < 0 || cc >= 128 (* we ensure it's inside of ascii *)
                                      then raise (NonAsciiChar (coordinates lexbuf c))
                                      else  "'" ^ Core.Char.to_string c ^ "'", rune_lit lexbuf c }
| newline { raise (UnfinishedRune (coordinates' lexbuf)) }
| ([^ '\''] _) as wrong { raise (TooManyForRune (coordinates lexbuf wrong)) }
| _   { raise (UnfinishedRune (coordinates' lexbuf)) }
| eof { raise (UnfinishedRune (coordinates' lexbuf)) }

(** here we handle raw strings
    it is the easiest because we just need to swallow chars.
 *)
and read_raw_string buf_inp buf =
  parse
| '`' { Buffer.add_char buf_inp '`'; end_coord lexbuf }
(* notice that we need to account for every new line *)
| newline as s { Buffer.add_string buf_inp s; Buffer.add_string buf s; Lexing.new_line lexbuf; read_raw_string buf_inp buf lexbuf }
| [^ '`' '\r' '\n' ] as c { let cc = Char.code c in
                            if cc < 0 || cc >= 128 (* we ensure it's inside of ascii *)
                            then raise (NonAsciiChar (coordinates lexbuf c))
                            else Buffer.add_char buf_inp c; Buffer.add_char buf c; read_raw_string buf_inp buf lexbuf }
| _ { raise (UnfinishedString (Sraw, coordinates' lexbuf)) }
| eof { raise (UnfinishedString (Sraw, coordinates' lexbuf)) }

(** here we handle interpreted strings
    we cannot reuse [read_rune] because the escape sequences between two kinds differ.
 *)
and read_interpreted_string buf_inp buf =
  parse
| '"' { Buffer.add_char buf_inp '"'; end_coord lexbuf }
(* let's first handle escape sequence first *)
| '\\' 'a'  { Buffer.add_string buf_inp "\\a"  ;  Buffer.add_char buf '\x07'; read_interpreted_string buf_inp buf lexbuf }
| '\\' 'b'  { Buffer.add_string buf_inp "\\b"  ;  Buffer.add_char buf '\x06'; read_interpreted_string buf_inp buf lexbuf }
| '\\' 'f'  { Buffer.add_string buf_inp "\\f"  ;  Buffer.add_char buf '\x0c'; read_interpreted_string buf_inp buf lexbuf }
| '\\' 'n'  { Buffer.add_string buf_inp "\\n"  ;  Buffer.add_char buf '\n'  ; read_interpreted_string buf_inp buf lexbuf }
| '\\' 'r'  { Buffer.add_string buf_inp "\\r"  ;  Buffer.add_char buf '\r'  ; read_interpreted_string buf_inp buf lexbuf }
| '\\' 't'  { Buffer.add_string buf_inp "\\t"  ;  Buffer.add_char buf '\t'  ; read_interpreted_string buf_inp buf lexbuf }
| '\\' 'v'  { Buffer.add_string buf_inp "\\v"  ;  Buffer.add_char buf '\x0b'; read_interpreted_string buf_inp buf lexbuf }
| '\\' '\\' { Buffer.add_string buf_inp "\\\\" ; Buffer.add_char buf '\\'   ; read_interpreted_string buf_inp buf lexbuf }
| '\\' '"'  { Buffer.add_string buf_inp "\\\"" ; Buffer.add_char buf '"'    ; read_interpreted_string buf_inp buf lexbuf }
| ('\\' _) as s { raise (UninterpretableEscape (coordinates lexbuf s)) }
(* then for literal chars *)
| [^ '\\' '"' '\r' '\n' ] as c { let cc = Char.code c in
                                 if cc < 0 || cc >= 128 (* we ensure it's inside of ascii *)
                                 then raise (NonAsciiChar (coordinates lexbuf c))
                                 else Buffer.add_char buf_inp c; Buffer.add_char buf c; read_interpreted_string buf_inp buf lexbuf }
(* we disallow newline inside of an interpreted string *)
| newline { raise (NewLineInInterpreted (coordinates' lexbuf)) }
| _     { raise (UnfinishedString (Sint, coordinates' lexbuf)) }
| eof     { raise (UnfinishedString (Sint, coordinates' lexbuf)) }
