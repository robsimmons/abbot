signature ELEMENT =
sig
  type t
  val default : t
  val equal : t * t -> bool
  val compare : t * t -> order
  val hash : t -> int
  val toString : t -> string
end
