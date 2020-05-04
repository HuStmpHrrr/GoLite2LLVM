(** this file converts GoLite literals to OCaml literals *)
open Tags
open Meta

let max_int32 = Big_int.big_int_of_int32 (Int32.max_int)
let min_int32 = Big_int.big_int_of_int32 (Int32.min_int)

exception IntParseError of string meta
exception IntParseOverflow of string meta
exception FloatParseError of string meta


let to_int32 (k : int_kind) s =
  let nary_bigint s n f =
    Core.String.fold s ~init:Big_int.zero_big_int
                     ~f:(fun acc c ->
                       if c = '_' then acc
                       else Big_int.add_int_big_int (f c) (Big_int.mult_int_big_int n acc)) in
  let convert rm n f =
    let r = nary_bigint (String.sub s.data rm (String.length s.data - rm)) n f in
    begin match Big_int.int32_of_big_int_opt r with
    | Some x -> x
    | None   -> raise (IntParseOverflow s)
    end in
  match k with
  | IDec -> convert 0 10 (fun c -> if c < '0' || c > '9'
                                   then raise (IntParseError s)
                                   else Char.code c - Char.code '0')
  | IBin -> convert 2 2 (fun c -> if c = '0' then 0
                                  else if c = '1' then 1
                                  else raise (IntParseError s))
  | IOct ->
     let skip = if s.data.[1] = 'o' || s.data.[1] = 'O' then 2 else 1 in
     convert skip 8 (fun c -> if c < '0' || c > '7'
                              then raise (IntParseError s)
                              else Char.code c - Char.code '0')
  | IHex -> convert 2 16 (fun c -> if c >= '0' && c <= '9'
                                   then Char.code c - Char.code '0'
                                   else if c >= 'a' && c <= 'f'
                                   then Char.code c - Char.code 'a' + 10
                                   else if c >= 'A' && c <= 'F'
                                   then Char.code c - Char.code 'A' + 10
                                   else raise (IntParseError s))


let to_float (k : float_kind) s =
  let rec read_until_dot f n acc i =
    if i >= String.length s.data then acc, i
    else
      match s.data.[i] with
      | '.'
        | 'e' | 'p'
        | 'E' | 'P' -> acc, i
      | '_'         -> read_until_dot f n acc (i + 1)
      | c           -> read_until_dot f n (n *. acc +. f c) (i + 1)
  and read_until_exp f n acc i e =
    if i >= String.length s.data then acc, i
    else
      match s.data.[i] with
      | '_'         -> read_until_exp f n acc (i + 1) e
      | 'e' | 'p'
        | 'E' | 'P' -> acc, i
      | c           -> read_until_exp f n (acc +. e *. f c) (i + 1) (e /. n)
  and read_exp acc i =
    if i >= String.length s.data then acc, i
    else
      match s.data.[i] with
      | '+' | '-' | '_'   -> read_exp acc (i + 1)
      | ('0' .. '9') as c -> read_exp (Big_int.add_int_big_int (Char.code c - Char.code '0') (Big_int.mult_int_big_int 10 acc)) (i + 1)
      | _                 -> raise (FloatParseError s)
  in
  match k with
  | FDec ->
     let conv c =
       if c < '0' || c > '9'
       then raise (FloatParseError s)
       else Char.code c - Char.code '0' in
     let conv' c    = float (conv c) in
     let integer, i = read_until_dot conv' 10. 0. 0 in
     let frac, i    = read_until_exp conv' 10.0 0. (if s.data.[i] = '.' then i + 1 else i) 0.1 in
     if i < String.length s.data && (s.data.[i] = 'e' || s.data.[i] = 'E')
     then
       let expo, _ = read_exp Big_int.zero_big_int (i + 1) in
       let ex      = if s.data.[i + 1] = '-'
                     then 10. ** Big_int.float_of_big_int (Big_int.minus_big_int expo)
                     else 10. ** Big_int.float_of_big_int expo in
       integer *. ex +. frac *. ex
     else 
       integer +. frac
  | FHex ->
     let conv c =
       if c >= '0' && c <= '9'
       then Char.code c - Char.code '0'
       else if c >= 'a' && c <= 'f'
       then Char.code c - Char.code 'a' + 10
       else if c >= 'A' && c <= 'F'
       then Char.code c - Char.code 'A' + 10
       else raise (FloatParseError s) in
     let conv' c    = float (conv c) in
     let integer, i = read_until_dot conv' 16. 0. 2 in
     let frac, i    = read_until_exp conv' 16.0 0. (if s.data.[i] = '.' then i + 1 else i) (1. /. 16.) in
     let expo, _    = read_exp Big_int.zero_big_int (i + 1) in
     let ex         = if s.data.[i + 1] = '-'
                      then 2. ** Big_int.float_of_big_int (Big_int.minus_big_int expo)
                      else 2. ** Big_int.float_of_big_int expo in
     integer *. ex +. frac *. ex
