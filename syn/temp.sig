signature TEMP =
sig
  type t

  (* creates a new, globally unique temp *)
  val new : string -> t

  (* tests whether two temps are equal *)
  val equal  : (t * t) -> bool

  (* compares two temps.  This is used to allow
     temps as keys into a hash table *)
  val compare : (t * t) -> order

  (* provides a string representation of the globally
     unique temp *)
  val toString : t -> string

  (* Default value (shouldn't be used, but necessary to match ELEMENT sig *)
  val default : t

  (* Provides a hash representation of the temp *)
  val hash : t -> int

  (* provides the string used to create the temp *)
  val toUserString : t -> string
end
