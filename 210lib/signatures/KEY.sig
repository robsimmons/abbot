signature EQKEY =
sig
  type t
  val equal : t * t -> bool
  val toString : t -> string
end

signature ORDKEY =
sig
  include EQKEY
  val compare : t * t -> order
end

signature HASHKEY =
sig
  include ORDKEY
  val hash : t -> int
end
