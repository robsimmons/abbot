structure UnitElt : ELEMENT =
struct
  type t = unit

  exception NYI

  val default = ()
  fun equal ((),()) = true
  fun compare ((),()) = raise NYI
  fun hash () = raise NYI
  fun toString () = "()"
end
