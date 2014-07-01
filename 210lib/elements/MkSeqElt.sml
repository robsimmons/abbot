functor MkSeqElt (structure Elt : ELEMENT
                  structure Seq : SEQUENCE) : ELEMENT =
struct
  type t = Elt.t Seq.seq

  val default : t = Seq.empty ()
  val equal = Seq.equal Elt.equal
  val compare = Seq.collate Elt.compare
  fun toString s = Seq.toString Elt.toString s

  fun hash s =
      let
        fun rehash (h, e) =
            Word.+ (Word.fromInt (Elt.hash e),
                    Word.* (h, 0wx17))
      in Word.toIntX (Seq.iter rehash 0wx50356BCB s)
      end
end
