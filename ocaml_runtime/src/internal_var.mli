open! Base

type 'var t =
  | Free_var of 'var
  | Bound_var of int
[@@deriving compare, equal, sexp]
