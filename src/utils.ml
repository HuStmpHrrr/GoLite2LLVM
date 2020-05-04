open Core
open Format

exception Break
exception Exit
exception Impossible

let comma_concat f l =
  String.concat ~sep:", " (List.map ~f:f l)

let init_last l =
  let rec helper l acc la =
    match l with
    | []      -> la, List.rev acc
    | x :: xs -> helper xs (la :: acc) x in
  match l with
  | []      -> None
  | x :: xs -> Some (helper xs [] x)

module Modules = struct
  module List = Core.List
  module Char = Core.Char
  module String = Core.String
end

module SMap = Map.Make (String)

let acc_map f i l =
  let i', l' = Core.List.fold_map l ~init:i ~f in
  i', List.concat l'

type fmt =
  { fmt : 'a. ('a, formatter, unit) format -> 'a }

let die (f : fmt -> unit) =
  f { fmt = fun x -> eprintf x };
  pp_print_newline err_formatter ();
  exit 1
