functor MkPairElt (structure EltA : ELEMENT
                   structure EltB : ELEMENT) : ELEMENT =
struct
  type t = EltA.t * EltB.t

  val default = (EltA.default, EltB.default)

  fun equal ((xa,xb),(ya,yb)) =
      EltA.equal (xa,ya) andalso EltB.equal (xb,yb)

  fun compare ((xa,xb),(ya,yb)) =
      case EltA.compare (xa,ya)
        of EQUAL => EltB.compare (xb,yb)
         | ord => ord

  fun hash (a,b) =
      Word.toIntX (Word.* (Word.+ (Word.fromInt (EltA.hash a), 0wxB),
                     Word.* (Word.+ (Word.fromInt (EltB.hash b), 0wx17),
                             0wx50356BCB)))

  fun toString (a,b) =
      "(" ^ EltA.toString a ^ "," ^ EltB.toString b ^ ")"
end
