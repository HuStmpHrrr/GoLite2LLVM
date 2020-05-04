open Lexing

type 'a meta = {
    start_l : int;
    start_c : int;
    end_l   : int;
    end_c   : int;
    data    : 'a
  }

let start_coord lexbuf = 
  let cpos = lexbuf.lex_curr_p
  and spos = lexbuf.lex_start_p in 
  cpos.pos_lnum, spos.pos_cnum - cpos.pos_bol

let end_coord lexbuf = 
  let cpos = lexbuf.lex_curr_p in
  cpos.pos_lnum, cpos.pos_cnum - cpos.pos_bol

let coordinates lexbuf data =
  let (sl, sc) = start_coord lexbuf
  and (el, ec) = end_coord lexbuf in
  {
    start_l = sl;
    end_l   = el;
    start_c = sc;
    end_c   = ec;
    data    = data;
  }

let coordinates' lexbuf = coordinates lexbuf ()

let end_coord_meta lexbuf =
  let (el, ec) = end_coord lexbuf in
  {
    start_l = el;
    end_l   = el;
    start_c = ec;
    end_c   = ec;
    data    = ();
  }

let meta_zero =
  {
    start_l = 0;
    start_c = 0;
    end_l   = 0;
    end_c   = 0;
    data    = ()
  }

let update_data m d =
  { m with data = d }

let offset_start_c m off =
  { m with start_c = m.start_c + off }

let meta_zero' d = update_data meta_zero d

let forget_data m = update_data m ()

let range m1 m2 d =
  {
    start_l = m1.start_l;
    start_c = m1.start_c;
    end_l   = m2.end_l;
    end_c   = m2.end_c;
    data    = d;
  }

let meta_str m =
  if m.start_l = m.end_l then
    Format.sprintf "line %d char %d-%d" m.start_l m.start_c m.end_c
  else
    Format.sprintf "line %d char %d-line %d char %d" m.start_l m.start_c m.end_l m.end_c
