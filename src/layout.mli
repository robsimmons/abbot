open! Core

module Indentation : sig
  type t =
    | Indent
    | No_indent
end


type t =
  | Atom of string
  | Atom_magnet_left of string
  | Atom_magnet_right of string
  | Atom_magnet_both of string
  | List of (Indentation.t * t) list

val to_string : t -> max_length:int -> string
