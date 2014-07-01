functor MkOptionElt (structure Elt : ELEMENT) : ELEMENT =
struct
  type t = Elt.t option

  val default = NONE

  fun equal (NONE, NONE) = true
    | equal (SOME x, SOME y) = Elt.equal (x, y)
    | equal _ = false

  fun compare (NONE, NONE) = EQUAL
    | compare (NONE, SOME _) = LESS
    | compare (SOME _, NONE) = GREATER
    | compare (SOME x, SOME y) = Elt.compare (x, y)

  fun hash NONE = 0
    | hash (SOME x) = Elt.hash x

  fun toString NONE = "NONE"
    | toString (SOME x) = "SOME (" ^ Elt.toString x ^ ")"
end
