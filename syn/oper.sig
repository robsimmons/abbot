signature OPERATOR =
sig
  type t

  val arity : t -> int list
  val equal : (t * t) -> bool
  val toString : t -> string
end
