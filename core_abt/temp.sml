structure Temp :> TEMP =
struct
  type t = string * int

  val counter = ref 0

  fun hash (_, id) = id

  fun new s = (s, (counter := !counter + 1; !counter))

  fun equal ((_, id1) : t, (_, id2)) = (id1 = id2)

  fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2)

  fun toString (s, id) = s ^ "@" ^ (Int.toString id)

  fun toUserString (s, id) = s

  structure Dict =
  RedBlackDict
    (structure Key =
     struct
     type t = t
     val eq = equal
     val compare = compare
     end)
end
