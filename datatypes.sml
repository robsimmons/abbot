structure Datatypes =
struct

open Util
open Analysis

(* Abbot sorts can't end with:
 * View
 * Var
 *
 * And can't contain underscores. *)

fun Big s = Char.toString (Char.toUpper (String.sub (s, 0)))^
            String.extract (s, 1, NONE)
fun BIG s = String.map Char.toUpper s

fun mutualvar s = s^"_var" 
fun internalvar s = Big s^"Var" 
fun externalvar s = Big s^".Var" 
fun internalvart s = internalvar s^".t"
fun externalvart s = externalvar s^".t"

(* External rep *)
fun shortview s = s^"View"

(* Internal rep *)
fun shortty s = s
fun fullty s = Big s ^".t"

fun tyvar s = "'"^s

fun voidcons s = Big s^"_Void"

(*
fun valencetoviewstr (ana: ana) srt (symvar, res) =
    let
        val res' = 
            if (#fixwith ana) (res, srt) 
            then tyvar s
            else fullty s
    in 
        if null symvar then res'
        else "("^String.concatWith " * " (map fullvar symvar) @ [res'])^")"
    end

*)


    
fun tyvarsofView (ana: ana) srt post = 
let in 
    case #mutual ana srt of
        [] => ""
      | [ s ] => " "^tyvar srt^post
      | srts => " ("^String.concatWith 
                         ", "
                         (map (fn srt => tyvar srt^post) srts)^")" 
end
                      
fun concretesofView (ana: ana) srt = 
let in 
    case #mutual ana srt of
        [] => ""
      | [ s ] => " "^srt
      | srts => " ("^String.concatWith ", " srts^")" 
end
                      
fun emitview (ana: ana) external srt = 
let 
    fun typeofBound (ana: ana) srt = 
        if #issrt ana srt then externalvar srt
        else fullty srt
                    
    fun typeofViewValence (ana: ana) srt (boundsrts, res) = 
        let 
            val res' = 
                if #mutualwith ana srt res
                then tyvar res
                else fullty res
        in
            if null boundsrts then res'
            else "("^String.concatWith
                         " * "
                         (map (typeofBound ana) boundsrts @ [res'])^")"
        end
            
    fun typeofViewConstructor (ana: ana) srt prelude arity = 
        String.concat 
            (transFirst 
                 (fn () => [])
                 (fn (prelude, arg) => [prelude^arg])
                 (" of ", " * ")
                 (map (typeofViewValence ana srt) arity))

    fun emitarm pre post NONE =
        emit [pre^"Var of "^(if external 
                                 then externalvart srt
                                 else internalvart srt)^post]
      | emitarm pre post (SOME oper) = 
        emit [pre^oper^
              typeofViewConstructor ana srt pre (#arity ana srt oper)^
              post]
    val pre = if external then "(* datatype" else "datatype"
    val post = if external then "   *)" else ""
    val fst = if external then " *  = " else " = "
    val nxt = if external then " *  | " else " | "
in
    emit [pre^tyvarsofView ana srt ""^" "^shortview srt];
    appSuper
        (fn () => emit [fst^voidcons srt^" of "^shortview srt])
        (emitarm fst post)
        ((emitarm fst "", emitarm nxt "", emitarm nxt post)) 
        ((if #binds ana srt srt then [NONE] else []) @
         map SOME (#opers ana srt));
    ()
end


(*
fun emitvars srt = 
let in
    emit ["signature "^BIG srt^"_VAR = ", "sig"];
    incr();
    emit ["type "^shortvar srt];
    emit ["type t = "^shortvar srt];
    emit ["val newvar: string -> "^shortvar srt];
    emit ["val equal: ("^shortvar srt^" * "^shortvar srt^") -> bool"];
    emit ["val compare: ("^shortvar srt^" * "^shortvar srt^") -> order"];
    emit ["val toString: "^shortvar srt^" -> string"];
    emit ["val hash: "^shortvar srt^" -> int"];
    emit ["val toUserString: "^shortvar srt^" -> string"];
    decr();
    emit ["end","","structure "^Big srt^"Var:> "^BIG srt^"_VAR = ","struct"];
    incr();
    emit ["type "^shortvar srt^" = string * int"];
    emit ["type t = "^shortvar srt];
    emit ["val counter = ref 0"];
    emit ["val default = (\"default\", 0)"];
    emit ["fun hash (_, id) = id"];
    emit ["fun newvar s = (s, (counter := !counter + 1; !counter))"];
    emit ["fun equal (x: t, y: t) = #2 x = #2 y"];
    emit ["fun compare (x: t, y: t) = Int.compare (#2 x, #2 y)"];
    emit ["fun toString (s, id) = s ^ \"@\" ^ Int.toString id"];
    emit ["fun toUserString (s, id) = s"];
    decr();
    emit ["end"];
    ()
end
*)

fun emitgensig issym srt = 
let val maybevar = if issym then "" else "Var"
    val typ = srt^maybevar
in  emit ["signature "^BIG srt^(if issym then "" else "_VAR")^" = ", "sig"];
    incr();
    emit ["type t = AbbotImpl."^Big srt^maybevar^"."^typ];
    emit ["type "^typ^" = AbbotImpl."^Big srt^maybevar^"."^typ];
    emit ["val new"^(if issym then "sym" else "var")^": string -> "^typ];
    emit ["val equal: ("^typ^" * "^typ^") -> bool"];
    emit ["val compare: ("^typ^" * "^typ^") -> order"];
    emit ["val toString: "^typ^" -> string"];
    emit ["val hash: "^typ^" -> int"];
    decr();
    emit ["end"];
    ()
end

val emitsymbolsig = emitgensig true
val emitvariablesig = emitgensig false

fun emitgenstruct issym srt =
let val maybevar = if issym then "" else "Var"
    val typ = srt^maybevar
    val cons = if issym then "Sym" else "Var"
in  emit ["structure "^Big srt^maybevar^" = ","struct"];
    incr();
    emit ["datatype "^typ^" = "^cons^" of string * int"];
    emit ["type t = "^srt^maybevar];
    emit ["val counter = ref 0"];
    emit ["val default = (\"default\", 0)"];
    emit ["fun hash ("^cons^" (_, id)) = id"];
    emit ["fun newsym s = "^cons^" (s, (counter := !counter + 1; !counter))"];
    emit ["fun equal ("^cons^" (_, x), "^cons^" (_, y)) = x = y"];
    emit ["fun compare ("^cons^" (_, x), "^cons^" (_, y)) = "^
          "Int.compare (x, y)"];
    emit ["fun toString ("^cons^" (s, id)) = s ^ \"@\" ^ Int.toString id"];
    emit ["fun toUserString ("^cons^" (s, id)) = s"];
    decr();
    emit ["end"];
    (if issym 
     then emit ["type "^srt^" = "^Big srt^"."^srt,""]
     else emit [""]);
    ()
end

val emitsymbolstruct = emitgenstruct true
val emitvariablestruct = emitgenstruct false

(*
fun emitsymbols (ana: ana) =
let in
    app emitsymbol (#symbs ana)
end
*)

fun emitusersymbols (ana: ana) =
let in
    if null (#symbs ana) then ()
    else 
        (emit ["(* Implementation of symbol sorts *)",""];
         app (fn srt => 
                 (emitsymbolsig srt;
                  emit ["structure "^Big srt^":> "^BIG srt^
                        " = AbbotImpl."^Big srt,""]))
             (#symbs ana);
         emit [""])
end

fun emituservariables (ana: ana) = 
let 
    val mkvars = List.filter 
                     (fn srt => #binds ana srt srt)
                     (List.concat (#sorts ana))
in
    if null (#symbs ana) then ()
    else 
        (emit ["(* Signatures for variables *)",""];
         app (fn srt => 
                 (emitvariablesig srt;
                  emit [""]))
             mkvars;
         emit [""])
end

fun emitimpls (ana: ana) srts = 
let in
    
    ()
end

fun emitabbotimplstruct (ana: ana) =
let in
    emit ["structure AbbotImpl =","struct"];
    incr ();
    app (emitimpls ana) (#sorts ana);
    decr ();
    emit ["end",""];
    ()
end

fun emituserstruct (ana: ana) srt = 
let 
    fun postwhere post srt =
    let in
        if (#binds ana srt srt)
        then (emit ["where type "^srt^" = AbbotImpl."^srt];
              emit ["where type Var."^srt^"Var "^
                    "= AbbotImpl."^Big srt^"Var."^srt^"Var"^post])
        else (emit ["where type "^srt^" = AbbotImpl."^srt^post])
    end
in
    emit ["signature "^BIG srt^" = ","sig"];
    incr ();
    (if (#binds ana srt srt) 
     then emit ["structure Var: "^BIG srt^"_VAR"] else ());
    emit ["datatype "^shortview srt^" = AbbotImpl."^Big srt^"."^shortview srt];
    emitview ana true srt;
    app (fn s' => emit ["type "^s'^" (* = "^fullty s'^" *)"])
        (#mutual ana srt);
    emit ["type t = "^srt,""];
    emit ["val into:  "^concretesofView ana srt^" "^shortview srt^" -> "
          ^srt];
    emit ["val out:    "^srt^" ->"^
          concretesofView ana srt^" "^shortview srt];
    emit ["val aequiv: "^srt^" * "^srt^" -> bool"];
    appFirst 
        (fn () => raise Fail "Can't fmap")
        (fn (prelude, srt) => 
            emit [prelude ^"("^tyvar srt^"1 -> "^tyvar srt^"2)"])
        ("val fmap:   ","         -> ")
        (#mutual ana srt);
    emit ["         ->"^
                     tyvarsofView ana srt "1"^" "^shortview srt^" ->"^
                     tyvarsofView ana srt "2"^" "^shortview srt];
    decr ();
    emit ["end","structure "^Big srt^": "^BIG srt];
    incr (); incr ();
    appSuper 
        (fn () => emit [" ="])
        (postwhere " = ")
        (postwhere "", postwhere "", postwhere " = ")
        (#mutual ana srt);
    decr (); decr (); 
    emit ["struct"];
    incr ();
    decr ();
    emit ["end",""];
    ()
end

fun implconstructor sym oper = "Impl_"^Big sym^"_"^oper
fun implbvar sym = "Impl_"^Big sym^"__BVAR"
fun implfvar sym = "Impl_"^Big sym^"__FVAR"

fun emitsortimpl (ana: ana) (pre, srt) =
let
    fun typeofValence ana srt (boundsrts, res) = 
        if null boundsrts then res
        else "("^String.concatWith 
                     " * " (map (fn _ => "string") boundsrts @ [res])^")"

    fun typeofConstructor (ana: ana) srt arity =
        String.concat
            (transFirst
                 (fn () => [])
                 (fn (prelude, arg) => [prelude^arg])
                 (" of ", " * ")
                 (map (typeofValence ana srt) arity))

    fun emitarm ana (pre, NONE) =  
        emit [pre^implbvar srt^" of IntInf.int"]
      | emitarm ana (pre, SOME NONE) = 
        emit [pre^implfvar srt^" of "^internalvart srt]
      | emitarm ana (pre, SOME (SOME oper)) =
        emit [pre^implconstructor srt oper^
              typeofConstructor ana srt (#arity ana srt oper)]
in 
    emit [pre^" "^srt];
    appFirst 
        (fn _ => raise Fail "Unimplemented: empty sorts")
        (emitarm ana)
        (" = "," | ")
        ((if (#binds ana srt srt) then [NONE, SOME NONE] else []) @
         map (SOME o SOME) (#opers ana srt));
    emit [""];
    ()
end

fun emitblockimpl (ana: ana) srts = 
let in
    emit ["(* Implementation of recursive block: "^
          String.concatWith ", " srts ^" *)", ""];
    emit ["(* Naive sort implementation *)"];
    emit ["local"];
    incr ();
    appFirst (fn _ => raise Fail "Invariant") (emitsortimpl ana) 
        ("datatype", "and") srts;
    decr ();
    emit ["in"];
    incr ();
    app (fn srt => emit ["type "^srt^" = "^srt]) srts;
    decr ();
    emit ["end"];
    emit [""];
    ()
end

fun doit (ana: ana) = 
let in
    emitusersymbols ana;
    emituservariables ana;
    emit ["(* Implementation of normal sorts *)", ""];
    app (emituserstruct ana) (List.concat (#sorts ana));
    emit ["(* Intentionally shadow internals *)"];
    emit ["structure AbbotImpl = struct end"];
    emit ["structure AbbotImpl = ", "struct"];
    incr ();
    emit ["(* All symbols *)"];
    app emitsymbolstruct (#symbs ana);
    emit ["(* All variables *)"];
    app emitvariablestruct 
        (List.filter 
             (fn srt => #binds ana srt srt) 
             (List.concat (#sorts ana)));
    app (emitblockimpl ana) (#sorts ana);
    decr ();
    emit ["end"];
    ()
end

val _ = doit Analysis.minalgol


(* val _ = emitview Analysis.goedel ("datatype", "exp") *)


end
