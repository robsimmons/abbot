structure RealElt : ELEMENT =
struct
  type t = Real.real

  val default = 0.0
  val equal = Real.==
  val compare = Real.compare
  val toString = Real.toString
  fun hash(v) = 
      let
        val {man=m, exp=_} = Real.toManExp v
        fun ihash i = Word.toIntX (Word.* (0wx50356BCB, Word.fromInt i))
      in ihash (round (m * 1000000000.0))
      end
end
