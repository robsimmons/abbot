structure Abbot = struct
  fun genfromfile (filename : string, name_parts_opt : string list option) =
      let
        val () = print "Parsing...\n"
        val parse_data = Parse.parsefile filename

        val filename' =
            if String.isSuffix ".abt" filename
            then filename
            else filename ^ ".abt"

        val (sig_name, struct_name) =
            case name_parts_opt of
                SOME name_parts =>
                (String.concatWith "_" (List.map AbbotCore.BIG name_parts),
                 String.concat (List.map AbbotCore.Big name_parts))
              | NONE =>
                let
                  val _ :: name :: _ =
                      List.rev
                        (String.tokens
                           (fn (#"/" | #".") => true | _ => false)
                           filename')
                in
                  (AbbotCore.BIG name ^ "_ABT", AbbotCore.Big name ^ "Abt")
                end

        val () = print "Analysis...\n"
        val ana = Analysis.analyze parse_data

        val () = print "Generating signature...\n"
        val stream = TextIO.openOut (filename' ^ ".sig")
        val _ = Util.write stream (fn () => AbbotUser.doit_user sig_name ana)
        val _ = Util.flush ()
        val _ = TextIO.closeOut stream
        val _ = use (filename' ^ ".sig")

        val () = print "Generating structure...\n"
        val stream = TextIO.openOut (filename' ^ ".sml")
        val _ = Util.write stream
                  (fn () => AbbotImpl.doit_impl sig_name struct_name ana)
        val _ = Util.flush ()
        val _ = TextIO.closeOut stream
        val _ = use (filename' ^ ".sml")
      in
        ()
      end
      handle Parse.Parse s => print s
end
