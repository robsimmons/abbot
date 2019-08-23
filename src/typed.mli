open! Core

(* CR wduff: "simple" "open" and "closed" are bad names. *)

module Kind : sig
  type _ t =
    | Simple : [ `Simple ] t
    | Open : [ `Open ] t
    | Closed : [ `Closed ] t

  module Or_poly : sig
    type _ t =
      | Poly : [ `Poly ] t
      | Simple : [ `Simple ] t
      | Open : [ `Open ] t
      | Closed : [ `Closed ] t
  end
end

module Packed_with_kind (X : T1) : sig
  type t = T : 'k Kind.t * 'k X.t -> t
end

module Packed_with_kind_or_poly (X : T1) : sig
  type t = T : 'k Kind.Or_poly.t * 'k X.t -> t
end

module Abt : sig
  type _ t =
    | Arg_use : string -> [ `Simple ] t
    | Builtin_abt_use : Builtin_abt.t * 'a t list -> 'a t
    | Simple_abt_use : string * 'a t list -> 'a t
    | Open_abt_use : string -> [ `Open ] t
    | Closed_abt_use : string -> _ t
    | Symbol_use : string -> _ t
    | Sort_use : string -> _ t
    | Prod : 'a t list -> 'a t
    | Symbol_binding : string -> [ `Open ] t
    | Sort_binding : string -> [ `Open ] t
    | Bind : [ `Open ] t * [ `Closed ] t -> [ `Closed ] t

  val sexp_of_t : _ t -> Sexp.t
  val compare : _ t -> _ t -> int

  val cast_poly : [ `Poly ] t -> 'a t
end

module Cases : sig
  type 'a t = (string * 'a Abt.t option) list

  val cast_poly : [ `Poly ] t -> 'a t

  module Packed : sig
    type 'a unpacked = 'a t
    type t = T : 'a Kind.t * 'a unpacked -> t
  end with type 'a unpacked := 'a t
end

module Defn_body : sig
  type t =
    | External_simple_abt
    | Internal_abt of Cases.Packed.t
    | Symbol
    | Sort of [ `Closed ] Cases.t
end

module Defn : sig
  type t =
    { name : string; args : string list; body : Defn_body.t }
  [@@deriving fields]
end
