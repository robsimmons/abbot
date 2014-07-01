structure Abbot = struct
  fun genfromfile (name : string) =
      let
        val parse_data = Parse.parsefile name
        val name' =
            if String.isSuffix ".abt" name
            then name
            else name ^ ".abt"

        val ana = Analysis.analyze parse_data

        val stream = TextIO.openOut (name' ^ ".sig")
        val _ = Util.write stream (fn () => AbbotUser.doit_user ana)
        val _ = Util.flush ()
        val _ = TextIO.closeOut stream
        val _ = use (name' ^ ".sig")

        val stream = TextIO.openOut (name' ^ ".sml")
        val _ = Util.write stream (fn () => AbbotImpl.doit_impl ana)
        val _ = Util.flush ()
        val _ = TextIO.closeOut stream
        val _ = use (name' ^ ".sml")
      in
        ()
      end
      handle Parse.Parse s => print s
end
