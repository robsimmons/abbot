(* Abbot: implementating abstract binding trees (___.abt.impl.sml) *)

structure AbbotImpl =
struct

open Util
open Analysis
open AbbotCore

fun emitimplview (ana: ana) srt = 
let in
    emit ["structure "^Big srt^" =","struct"];
    incr ();
    emitview ana false srt;
    emit ["","val fmap = fn _ => raise Fail \"Unimpl\""];
    decr ();
    emit ["end",""];
    ()
end

(* Symbols and variables: effectively the same implementation *)
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
    emit ["fun new"^(if issym then "sym" else "var")^" s"^
          " = "^cons^" (s, (counter := !counter + 1; !counter))"];
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

(* Actual implementation of sorts *)
(* Naive implementation of locally nameless *)
fun implconstructor srt oper = "Impl_"^Big srt^"_"^oper
fun implbvar srt = "Impl_"^Big srt^"_BoundVar"
fun implfvar srt = "Impl_"^Big srt^"_Var"
fun implfold srt = "Impl_"^Big srt

fun emitdatatypeimpl_naive (ana: ana) (pre, srt) =
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
(*        emit [pre^implfold srt^" of"^concretesofView ana srt^" "^
              fullview srt] *)
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

(* Emit a mutually-interdependent block of *)
fun emitblockimpl (ana: ana) srts = 
let val dummy = " = fn _ => raise Fail \"Unimpl\""
in
    emit ["(* Implementation of recursive block: "^
          String.concatWith ", " srts ^" *)", ""];
    app (emitimplview ana) srts;
    emit ["(* Naive and minimal implementation *)"];
    emit ["local"];
    incr ();
    appFirst (fn _ => raise Fail "Invariant") (emitdatatypeimpl_naive ana) 
        ("datatype", "and") srts;
    decr ();
    emit ["in"];
    incr ();
    app (fn srt => emit ["type "^srt^" = "^srt]) srts;
    app (fn srt => emit ["val out_"^srt^dummy]) srts;
    app (fn srt => emit ["val into_"^srt^dummy]) srts;
    app (fn srt => emit ["val aequiv_"^srt^dummy]) srts;
    app (fn srt => emit ["val toString_"^srt^dummy]) srts;
    app (fn varsrt =>
            app (fn srt => emit ["val free_"^varsrt^"_"^srt^dummy]) srts)
        (#varin ana (hd srts));
    app (fn symsrt =>
            app (fn srt => emit ["val free_"^symsrt^"_"^srt^dummy]) srts)
        (#symin ana (hd srts));
    decr ();
    emit ["end","","(* Derived functions *)"];
    (* Takes advantage of the fact that 'varin' has to be the same across
     * a block of mutually-defined sorts *)
    app (fn varsrt =>
            app (fn srt => emit ["val subst_"^varsrt^"_"^srt^dummy]) srts)
        (#varin ana (hd srts));
    emit [""];
    ()
end

(* We want to put this in the abt.impl.sml file in order to have
 * the user structure simply ascribe to an existing signature *)
fun emitfinalimpl (ana: ana) srt = 
let in
    emit ["structure "^Big srt^"Impl =","struct"];
    incr();
    emit ["type t = "^srt];
    app (fn s' => emit ["type "^s'^" = "^s']) (#mutual ana srt);
    app (fn s' => if (#binds ana srt s') 
                  then emit ["type "^s'^"Var = "^internalvart s']
                  else ()) (#mutual ana srt);
    emit ["open "^Big srt];
    (if #binds ana srt srt 
     then emit ["structure Var = "^internalvar srt]
     else ());
    emit ["val into = into_"^srt];
    emit ["val out = out_"^srt];
    emit ["val aequiv = aequiv_"^srt];
    emit ["val toString = toString_"^srt];
    decr();
    emit ["end",""];
    ()
end

fun doit_impl (ana: ana) = 
let in
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
    emit ["(* Rebind structs with full contents *)"];
    app (emitfinalimpl ana) (List.concat (#sorts ana));
    decr ();
    emit ["end"];
    ()
end

end
