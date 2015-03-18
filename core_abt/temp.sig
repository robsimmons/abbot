signature TEMP =
sig
  type t

  (* Creates a new, globally unique temp. *)
  val new : string -> t

  (* Tests whether two temps are equal. *)
  val equal  : (t * t) -> bool

  (* Compares two temps. This is used to allow temps as keys into a table. *)
  val compare : (t * t) -> order

  (* Provides a string representation of the globally unique temp. *)
  val toString : t -> string

  (* Provides a hash representation of the temp. *)
  val hash : t -> int

  (* Provides the string used to create the temp. *)
  val toUserString : t -> string

  structure Dict : DICT where type key = t
end
