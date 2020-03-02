open! Core

module type S0 = sig
  type t [@@deriving sexp_of]

  val apply_renaming : Renaming.t -> 'acc -> t -> 'acc * t
  val subst : 'sort -> 'value -> 'var -> t -> t
end

module type S1 = sig
  type 'a t [@@deriving sexp_of]

  val apply_renaming
    : (Renaming.t -> 'acc -> 'a1 -> 'acc * 'a2) -> Renaming.t -> 'acc -> 'a1 t -> 'acc * 'a2 t

  val subst : ('sort -> 'value -> 'var -> 'a -> 'a) -> 'sort -> 'value -> 'var -> 'a t -> 'a t
end

module Unit : S0 with type t = unit
module Int : S0 with type t = int
module Int64 : S0 with type t = Int64.t
module Char : S0 with type t = char
module String : S0 with type t = string

module Option : S1 with type 'a t = 'a option
module List : S1 with type 'a t = 'a list
module String_map : S1 with type 'a t = 'a Core.String.Map.t
