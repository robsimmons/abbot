open! Core

type t =
  | Free_var of Temp.t
  | Bound_var of int
[@@deriving compare, sexp]
