(* Abbot: emitting user interface (___.abt.user.sml) *)

functor AbbotUser (Analysis : ANALYSIS) =
struct

open Util
open Analysis
structure AC = AbbotCore (Analysis)
open AC

(* Symbols and variables: basically the same thing *)
fun emitgensig issym srt =
let val maybevar = if issym then "" else "Var"
    val typ = srt^maybevar
in  emit ["signature "^BIG srt^(if issym then "" else "_VAR")^" = ", "sig"];
    incr();
    emit ["type "^typ^(if issym
                       then (" = AbbotImpl."^Big srt^maybevar^"."^typ)
                       else "")];
    emit ["type t = "^typ];
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

fun emituservariables () =
let
    val mkvars = List.filter
                     (fn srt => binds srt srt)
                     (StringTable.Seq.toList
                        (StringTable.Set.toSeq
                           (StringTable.domain sorts)))
in
    if null mkvars then ()
    else
        (emit ["(* Signatures for variables *)",""];
         app (fn srt =>
                 (emitvariablesig srt;
                  emit [""]))
             mkvars;
         emit [""])
end

fun emitusersymbols () =
let in
    if null symbs then ()
    else
        (emit ["(* Implementation of symbol sorts *)",""];
         app (fn srt =>
                 (emitsymbolsig srt;
                  emit ["structure "^Big srt^":> "^BIG srt^
                        " = AbbotImpl."^Big srt,""]))
             symbs;
         emit [""])
end

(* Sorts and variable sorts to strings *)
fun ss srt s' =
    if (mutualwith srt s')
    then (s')
    else (Big s'^"."^s')
fun ssv srt varsrt =
    if (mutualwith srt varsrt)
    then (varsrt^"Var")
    else (Big varsrt^".Var."^varsrt^"Var")

(* The convienece constructors *)
fun emitconvienenceconstructor srt (oper : Syntax.oper) =
let
    fun typeofBound boundsrt =
        if issrt boundsrt
        then ssv srt boundsrt (* Variable *)
        else ss srt boundsrt (* Symbol *)

    fun typeofValence (boundsrts, res) =
        if null boundsrts then ss srt res
        else "("^String.concatWith
                     " * "
                     (map typeofBound boundsrts @ [ss srt res])^")"
    val args = map typeofValence (#arity oper)
in
    if null args
    then emit ["val "^ #name oper^"': "^srt]
    else emit ["val "^ #name oper^"': "^String.concatWith " * " args^" -> "^srt]
end

(* The sealing for the user struct is the most interesting part... *)
fun emituserstruct srt =
let
    fun emitwhereclauses s' =
    let in
        if (binds srt s')
        then (emit ["where type "^s'^" = AbbotImpl."^s'];
              emit ["where type "^s'^"Var "^
                    "= AbbotImpl."^Big s'^"Var."^s'^"Var"])
        else (emit ["where type "^s'^" = AbbotImpl."^s'])
    end
in
    emit ["signature "^BIG srt^" = ","sig"];
    incr ();
    app (fn s' =>
            (emit ["type "^s'^" (* = "^fullty s'^" *)"];
             (if (binds srt s')
              then emit ["type "^s'^"Var (* = "^externalvart s'^" *)"]
              else ())))
        (mutual srt);
    emit ["type t = "^srt,""];

    (if (binds srt srt)
     then emit ["structure Var: "^BIG srt^"_VAR where type "^
                srt^"Var = "^srt^"Var"] else ());
    emit ["datatype "^shortview srt^
          " = datatype AbbotImpl."^Big srt^"."^shortview srt];
    emitview true srt;
    emit [""];
    (if (binds srt srt)
     then emit ["val Var' : "^srt^"Var -> "^srt] else ());
    app (emitconvienenceconstructor srt)
        (valOf (StringTable.find sorts srt));
    emit [""];

    emit ["val into: "^concretesofView srt^" "^shortview srt^" -> "
          ^srt];
    emit ["val out: "^srt^" ->"^
          concretesofView srt^" "^shortview srt];
    emit ["val aequiv: "^srt^" * "^srt^" -> bool"];
    emit ["val toString: "^srt^" -> string"];
    (if binds srt srt
     then emit ["val subst: "^srt^" -> "^srt^"Var -> "^srt^" -> "^srt (*,
                "val freevars: "^srt^" -> "^srt^"Var list" *)]
     else ());
    app (fn s' =>
            if s' = srt then ()
            else emit ["val subst"^Big s'^": "^ss srt s'^" -> "^
                       ssv srt s'^" -> "^
                       srt^" -> "^srt (*,
                       "val free"^Big s'^"Vars: "^srt^" -> "^
                       ssv srt s'^" list" *)])
        (varin srt);
    (* app (fn s' => emit ["val free"^Big s'^": "^srt^" -> "^Big s'^"."^s'^" list"]) *)
        (symin srt);
    appFirst
        (fn () => raise Fail "Can't fmap")
        (fn (prelude, srt) =>
            emit [prelude ^"("^tyvar srt^"1 -> "^tyvar srt^"2)"])
        ("val fmap: ","       -> ")
        (mutual srt);
    emit ["       ->"^
          tyvarsofView srt "1"^" "^shortview srt^" ->"^
          tyvarsofView srt "2"^" "^shortview srt];
    decr ();
    emit ["end","structure "^Big srt^": "^BIG srt];
    incr (); incr ();
    app emitwhereclauses (mutual srt);
    emit ["= AbbotImpl."^Big srt,""];
    decr (); decr ();
    ()
end

fun doit_user () =
let in
    emitusersymbols ();
    emituservariables ();
    emit ["(* Implementation of normal sorts *)", ""];
    app emituserstruct
        (StringTable.Seq.toList
           (StringTable.Set.toSeq
              (StringTable.domain sorts)));
    emit ["(* Intentionally shadow internals *)"];
    emit ["structure AbbotImpl = struct end"];
    ()
end

end
