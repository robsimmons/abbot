open! Core

module type S0 = sig
  type t [@@deriving sexp_of]

  val fold_map : 'acc -> t -> 'acc * t
  val apply_subst : 'subst -> t -> t
end

module type S1 = sig
  type 'a t [@@deriving sexp_of]

  val fold_map : ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a t -> 'acc * 'b t
  val apply_subst : ('subst -> 'a -> 'b) -> 'subst -> 'a t -> 'b t
end

module type External_abts = sig
  module Unit : S0 with type t = unit
  module Int : S0 with type t = int
  module Int64 : S0 with type t = Int64.t
  module Char : S0 with type t = char
  module String : S0 with type t = string

  module Option : S1 with type 'a t = 'a option
  module List : S1 with type 'a t = 'a list
  module String_map : S1 with type 'a t = 'a Core.String.Map.t
end
