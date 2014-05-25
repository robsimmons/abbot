structure BoolElt : ELEMENT =
struct
  type t = Bool.bool

  exception NYI

  val default = true
  val equal : t * t -> bool = op=
  fun compare _ = raise NYI
  fun hash _ = raise NYI
  val toString = Bool.toString
end
