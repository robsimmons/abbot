open! Core

module type S = sig
  type t [@@deriving compare, hash, sexp]

  include Comparable.S with type t := t
  include Hashable.S with type t := t

  (* Creates a new, globally unique temp. *)
  val create : string -> t

  (* Provides the string used to create the temp. *)
  val name : t -> string
end
