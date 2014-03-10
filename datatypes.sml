CM.make "sources.cm";

fun doitall (ana: Analysis.ana) name = 
let 
    val stream = TextIO.openOut (name^".abt.impl.sml")
    val _ = Util.write stream (fn () => AbbotImpl.doit_impl ana)
    val _ = Util.flush ()
    val _ = TextIO.closeOut stream
    val _ = use (name^".abt.impl.sml")
    
    val stream = TextIO.openOut (name^".abt.user.sml")
    val _ = Util.write stream (fn () => AbbotUser.doit_user ana)
    val _ = Util.flush ()
    val _ = TextIO.closeOut stream
    val _ = use (name^".abt.user.sml")
in
    ()
end;
    
doitall Analysis.minalgol "minalgol";
doitall Analysis.godel "godel";
