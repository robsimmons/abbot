structure Parse =
struct
    exception Parse of string

    structure AbtLrVals = AbtLrValsFun(structure Token = LrParser.Token)
    structure Lex = Abt_LexFun (structure Tokens = AbtLrVals.Tokens)
    structure AbtP = Join (structure ParserData = AbtLrVals.ParserData
                           structure Lex = Lex
                           structure LrParser = LrParser)

    fun stringreader s =
      let
        val pos = ref 0
        val remainder = ref (String.size s)
        fun min(a, b) = if a < b then a else b
      in
        fn n =>
           let
             val m = min(n, !remainder)
             val s = String.substring(s, !pos, m)
             val () = pos := !pos + m
             val () = remainder := !remainder - m
           in
             s
           end
      end

    fun error (s, pos, pos') = raise Parse s

    fun parse text =
      let
        val lexer =  AbtP.makeLexer (stringreader text)
        val (res, _) = AbtP.parse (1, lexer, error, ())
      in
        res
      end

    fun parsefile filename =
      let
        val str = TextIO.openIn filename
        fun loop NONE xs = (TextIO.closeIn str; String.concat (rev xs))
          | loop (SOME x) xs = loop (TextIO.inputLine str) (x :: xs)
      in
        parse (loop (TextIO.inputLine str) [])
      end

end
