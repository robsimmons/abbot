structure Abbot = struct
  fun genFromFile
        (fromFile : string,
         namePartsOpt : string list option,
         toFileOpt : string option) =
    let
      val () = print "Parsing...\n"
      val parse_data = Parse.parsefile fromFile

      val toFile =
          case toFileOpt of
              NONE => fromFile
            | SOME toFile => toFile

      val (sigName, structName) =
          case namePartsOpt of
              SOME parts =>
              (String.concatWith "_" (List.map AbbotCore.BIG parts),
               String.concat (List.map AbbotCore.Big parts))
            | NONE =>
              let
                val tail :: _ =
                    List.rev
                      (String.tokens (fn #"/" => true | _ => false) toFile)

                val parts =
                    String.tokens
                      (fn (#"." | #"-" | #"_") => true | _ => false)
                      tail
              in
                (String.concatWith "_" (List.map AbbotCore.BIG parts) ^ "_ABT",
                 String.concat (List.map AbbotCore.Big parts) ^ "Abt")
              end

      val () = print "Analysis...\n"
      val ana = Analysis.analyze parse_data

      val () = print "Generating signature...\n"
      val stream = TextIO.openOut (toFile ^ ".sig")
      val _ = Util.write stream (fn () => AbbotUser.doit_user sigName ana)
      val _ = Util.flush ()
      val _ = TextIO.closeOut stream
      val _ = use (toFile ^ ".sig")

      val () = print "Generating structure...\n"
      val stream = TextIO.openOut (toFile ^ ".sml")
      val _ = Util.write stream
                         (fn () => AbbotImpl.doit_impl sigName structName ana)
      val _ = Util.flush ()
      val _ = TextIO.closeOut stream
      val _ = use (toFile ^ ".sml")
    in
      ()
    end
    handle Parse.Parse s => print s
end
