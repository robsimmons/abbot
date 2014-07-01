functor MkListElt (structure Elt : ELEMENT) =
struct
  exception NYI

  val default = []
  type t = int list
  val equal : (int list * int list) -> bool = op=
  fun compare _ = raise NYI
  fun hash _ = raise NYI
  fun toString xs =
      "[" ^ String.concatWith "," (List.map Int.toString xs) ^ "]"
end
