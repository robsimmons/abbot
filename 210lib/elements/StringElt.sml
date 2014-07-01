structure StringElt : ELEMENT = 
struct
  type t = String.string

  val default = ""
  val equal : t * t -> bool = op=
  val compare = String.compare
  fun hash s = 
      let
        fun subs i = Word.fromInt (Char.ord (String.sub (s,i)))
        val c = Word.fromInt 65599
        fun hash'(i,h) = 
            if i < 0 then h else hash' (i-1, subs i + h * c)
      in Word.toIntX (hash'(String.size s -1, Word.fromInt 0))
      end
  fun toString s = "\"" ^ String.toString s ^ "\""
end
