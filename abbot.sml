structure Abbot = struct
  fun genFromFile
        (fromFile : string,
         namePartsOpt : string list option,
         toDir : string,
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
                val parts =
                    String.tokens
                      (fn (#"." | #"-" | #"_") => true | _ => false)
                      toFile
              in
                (String.concatWith "_" (List.map AbbotCore.BIG parts),
                 String.concat (List.map AbbotCore.Big parts))
              end

      val () = print "Analysis...\n"
      val ana = Analysis.analyze parse_data

      val () = print "Generating signature...\n"
      val stream = TextIO.openOut (toDir ^ "/" ^ toFile ^ ".sig")
      val _ = Util.write stream (fn () => AbbotUser.doit_user sigName ana)
      val _ = Util.flush ()
      val _ = TextIO.closeOut stream

      val () = print "Generating structure...\n"
      val stream = TextIO.openOut (toDir ^ "/" ^ toFile ^ ".sml")
      val _ = Util.write stream
                (fn () => AbbotImpl.doit_impl sigName structName ana)
      val _ = Util.flush ()
      val _ = TextIO.closeOut stream

      val () = print "Pulling in support code...\n"
      val stream = TextIO.openOut (toDir ^ "/abt.cm")
      val _ =
          Util.write stream
            (fn () =>
              Util.emit
                ["Group\n"
                 ^ "  signature " ^ sigName ^ "\n"
                 ^ "  structure " ^ structName ^ "\n"
                 ^ "is\n"
                 ^ "  $/basis.cm\n"
                 ^ "  temp.sig\n"
                 ^ "  temp.sml\n"
                 ^ "  symbol.sig\n"
                 ^ "  symbol.sml\n"
                 ^ "  abt.sig\n"
                 ^ "  abt.sml\n"
                 ^ "  " ^ toFile ^ ".sig\n"
                 ^ "  " ^ toFile ^ ".sml\n"])
      val _ = Util.flush ()
      val _ = TextIO.closeOut stream
    in
      ()
    end
    handle Parse.Parse s => print s
end
