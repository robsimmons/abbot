open! Base

module type S0 = sig
  type t [@@deriving sexp_of]
end

module type S1 = sig
  type 'a t [@@deriving sexp_of]

  val map : ('a -> 'b) -> 'a t -> 'b t
  val fold_map : ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a t -> 'acc * 'b t
end

module type External_abts = sig
  module Unit : S0 with type t = unit
  module Bool : S0 with type t = bool
  module Int : S0 with type t = int
  module Int64 : S0 with type t = Int64.t
  module Char : S0 with type t = char
  module String : S0 with type t = string

  module Option : S1 with type 'a t = 'a option
  module List : S1 with type 'a t = 'a list
  module String_map : S1 with type 'a t = 'a Core.String.Map.t
end
