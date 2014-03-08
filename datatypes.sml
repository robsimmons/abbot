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
fun structvar s = Big s^".Var" 
fun fullvar s = structvar s^".t"

(* External rep *)
fun shortview s = s^"View"
fun fullview s = structvar s^".t"

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

fun typeofBound (ana: ana) srt = 
    if #issrt ana srt then fullvar srt
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
             (fn (prelude, arg) =>
                 [prelude^arg])
             (" of ", " * ")
             (map (typeofViewValence ana srt) arity))
    
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
                      
fun emitview (ana: ana) srt = 
let in
    emit ["datatype"^tyvarsofView ana srt ""^" "^shortview srt];
    appFirst 
        (fn () => emit [" = "^voidcons srt^" of "^shortview srt])
        (fn (prelude,const) => 
            emit [prelude^const^
                  typeofViewConstructor ana srt prelude (#arity ana srt const)])
        (" = "," | ")
        ((#opers ana) srt)
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

fun emitsymbol srt = 
let in
    emit ["signature "^BIG srt^" = ", "sig"];
    incr();
    emit ["type "^srt];
    emit ["type t = "^srt];
    emit ["val newsym: string -> "^srt];
    emit ["val equal: ("^srt^" * "^srt^") -> bool"];
    emit ["val compare: ("^srt^" * "^srt^") -> order"];
    emit ["val toString: "^srt^" -> string"];
    emit ["val hash: "^srt^" -> int"];
    emit ["val toUserString: "^srt^" -> string"];
    decr();
    emit ["end","","structure "^Big srt^"Impl:> "^BIG srt^" = ","struct"];
    incr();
    emit ["type "^srt^" = string * int"];
    emit ["type t = "^srt];
    emit ["val counter = ref 0"];
    emit ["val default = (\"default\", 0)"];
    emit ["fun hash (_, id) = id"];
    emit ["fun newsym s = (s, (counter := !counter + 1; !counter))"];
    emit ["fun equal (x: t, y: t) = #2 x = #2 y"];
    emit ["fun compare (x: t, y: t) = Int.compare (#2 x, #2 y)"];
    emit ["fun toString (s, id) = s ^ \"@\" ^ Int.toString id"];
    emit ["fun toUserString (s, id) = s"];
    decr();
    emit ["end",""];
    ()
end

fun emitsymbols (ana: ana) =
let in
    app emitsymbol (#symbs ana)
end

fun emitusersymbols (ana: ana) =
let in
    if null (#symbs ana) then ()
    else 
        (emit ["(* Symbol sorts, which match signature SYMBOL *)"];
         app (fn srt => 
                 emit ["structure "^Big srt^" = "^Big srt^"Impl"])
             (#symbs ana);
         emit [""])
end

fun emituserstruct (ana: ana) srt = 
let in
    emit ["signature "^BIG srt^" = ","sig"];
    incr ();
    emit ["datatype "^shortview srt^" = AbbotImpl."^shortview srt^" (*"];
    emitview ana srt;
    emit ["*)",""];
    app (fn s' => emit ["type "^s'^" (* "^fullty s'^" *)"])
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
        (fn srt => emit ["where type "^srt^" = AbbotImpl."^srt])
        ((fn srt => emit ["where type "^srt^" = AbbotImpl."^srt]),
         (fn srt => emit ["where type "^srt^" = AbbotImpl."^srt]),
         (fn srt => emit ["where type "^srt^" = AbbotImpl."^srt^" = "]))
        (#mutual ana srt);
    decr (); decr (); 
    emit ["struct"];
    incr ();
    decr ();
    emit ["end",""];
    ()
end

fun doit (ana: ana) = 
let in
    emitsymbols ana;
    emit ["(* Complicated implementation goes here *)",""];
    emitusersymbols ana;
    emit ["(* Implementation of sorts *)"];
    app (emituserstruct ana) (List.concat (#sorts ana));
    emit ["structure AbbotImpl = struct end"];
    ()
end

val _ = doit Analysis.minalgol


(* val _ = emitview Analysis.goedel ("datatype", "exp") *)


end
