(* Core functionality about the way abbot maps sorts to SML types *)

functor AbbotCore (Analysis : ANALYSIS) =
struct

open Util
open Analysis

fun Big s = Char.toString (Char.toUpper (String.sub (s, 0)))^
            String.extract (s, 1, NONE)
fun BIG s = String.map Char.toUpper s

fun internalvar s = Big s^"Var"
fun externalvar s = Big s^".Var"
fun internalvart s = internalvar s^".t"
fun externalvart s = externalvar s^".t"

(* External rep *)
fun shortview s = s^"View"
fun fullview s = Big s^"."^s^"View"

(* Internal rep *)
fun shortty s = s
fun fullty s = Big s ^".t"

fun tyvar s = "'"^s

fun voidcons s = Big s^"_Void"

fun tyvarsofView srt post =
let in
    case mutual srt of
        [] => ""
      | [ s ] => " "^tyvar srt^post
      | srts => " ("^String.concatWith
                         ", "
                         (map (fn srt => tyvar srt^post) srts)^")"
end

fun concretesofView srt =
let in
    case mutual srt of
        [] => ""
      | [ s ] => " "^srt
      | srts => " ("^String.concatWith ", " srts^")"
end

fun emitview external srt =
let
    val showvar = if external then externalvar else internalvar
    val showvart = if external then externalvart else internalvart

    fun typeofBound srt =
        if issrt srt then showvart srt
        else (if external then fullty srt else srt)

    fun typeofViewValence srt (boundsrts, res) =
        let
          val res' =
              if mutualwith srt res
              then tyvar res
              else (if external then fullty res else res)
        in
            if null boundsrts then res'
            else "("^String.concatWith
                         " * "
                         (map typeofBound boundsrts @ [res'])^")"
        end

    fun typeofViewConstructor srt prelude arity =
        String.concat
            (transFirst
                 (fn () => [])
                 (fn (prelude, arg) => [prelude^arg])
                 (" of ", " * ")
                 (map (typeofViewValence srt) arity))

    fun emitarm pre post NONE =
        emit [pre^"Var of "^showvart srt^post]
      | emitarm pre post (SOME (oper : Syntax.oper)) =
        emit [pre^ #name oper^
              typeofViewConstructor srt pre (#arity oper)^
              post]
    val pre = if external then "(* datatype" else "datatype"
    val post = if external then "   *)" else ""
    val fst = if external then " *  = " else " = "
    val nxt = if external then " *  | " else " | "
in
    emit [pre^tyvarsofView srt ""^" "^shortview srt];
    appSuper
        (fn () => emit [fst^voidcons srt^" of "^shortview srt])
        (emitarm fst post)
        ((emitarm fst "", emitarm nxt "", emitarm nxt post))
        ((if binds srt srt then [NONE] else []) @
         map SOME (valOf (StringTable.find sorts srt)));
    ()
end

end
