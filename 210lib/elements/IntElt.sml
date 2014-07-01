structure IntElt : ELEMENT =
struct
  type t = Int.int

  val default = 0
  val equal : (int*int) -> bool = op=
  val compare = Int.compare
  fun hash i = Word.toIntX (Word.* (0wx50356BCB, Word.fromInt i))
  val toString = Int.toString
end
