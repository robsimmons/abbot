CM.make "sources.cm";

fun doitall (ana: Analysis.ana) name = 
let 
    val stream = TextIO.openOut ("examples/"^name^".abt.impl.sml")
    val _ = Util.write stream (fn () => AbbotImpl.doit_impl ana)
    val _ = Util.flush ()
    val _ = TextIO.closeOut stream
    val _ = use ("examples/"^name^".abt.impl.sml")
    
    val stream = TextIO.openOut ("examples/"^name^".abt.user.sml")
    val _ = Util.write stream (fn () => AbbotUser.doit_user ana)
    val _ = Util.flush ()
    val _ = TextIO.closeOut stream
    val _ = use ("examples/"^name^".abt.user.sml")
in
    ()
end;
    
doitall Analysis.godel "godel";
doitall Analysis.minalgol "minalgol";
doitall Analysis.systemf "systemf";
