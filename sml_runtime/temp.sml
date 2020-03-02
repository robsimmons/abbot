structure Temp :> TEMP = struct
  type t = string * int

  val counter = ref 0

  fun create s = (s, (counter := !counter + 1; !counter))

  fun hash (_, id) = Word.fromInt id

  fun eq ((_, (id1 : int)), (_, (id2 : int))) = id1 = id2

  fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2)

  fun name (s, _) = s
end
