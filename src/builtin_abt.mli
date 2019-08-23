open! Core

type t [@@deriving compare, enumerate, sexp]

val of_name : string -> t option
val name : t -> string
val arity : t -> int
val core_type : t -> string
val module_name : t -> string
