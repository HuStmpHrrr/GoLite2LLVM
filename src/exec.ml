include Syntax
include Semantics
include Typed
open Lexing
open Lexer
open Parser

module I = struct
  include Parser.MenhirInterpreter
  include Parser.Incremental
  open Lexing

  let go_lexbuf_to_supplier lexer lexbuf : supplier =
    let prev = ref None in
    fun () ->
    let startp = lexbuf.lex_curr_p in
    let token = lexer !prev lexbuf in
    let endp = lexbuf.lex_curr_p in
    prev := Some token;
    token, startp, endp

  let go_lexbuf_read () =
    let prev = ref None in
    fun lexbuf ->
    let token = read !prev lexbuf in
    prev := Some token;
    token
end

let parse_program s =
  let lexbuf = Lexing.from_string s in
  Untyped.remove_paren (Untyped.check_continue_break (program (I.go_lexbuf_read ()) lexbuf))

let typed_program s = tc_program (parse_program s)

let typed_program_file f =
  typed_program (Core.In_channel.read_all f)
