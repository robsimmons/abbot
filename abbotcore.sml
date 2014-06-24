(* Core functionality about the way abbot maps sorts to SML types *)

structure AbbotCore =
struct

open Util
infixr 0 >>
open Analysis
open AbstractSML

fun Big s = Char.toString (Char.toUpper (String.sub (s, 0)))
            ^ String.extract (s, 1, NONE)
fun BIG s = String.map Char.toUpper s

fun internalvar s = Big s ^ "Var"
fun externalvar s = Big s ^ ".Var"
fun internalvart s = internalvar s ^ ".t"
fun externalvart s = externalvar s ^ ".t"

(* External rep *)
fun shortview s = s ^ "View"
fun fullview s = Big s ^ "." ^ s ^ "View"

(* Internal rep *)
fun shortty s = s
fun fullty s = Big s ^ ".t"

fun tyvar s = "'" ^ s

fun voidcons s = Big s ^ "_Void"

fun tyvarsofView (ana : ana) srt post =
    List.map (fn srt => TypeVar ("'" ^ srt)) (#mutual ana srt)

fun concretesofView (ana : ana) srt =
    List.map TypeVar (#mutual ana srt)

fun emitview (ana : ana) external srt =
    let
      val showvar = if external then externalvar else internalvar
      val showvart = if external then externalvart else internalvart

      fun typeofBound (ana : ana) srt =
          if #issrt ana srt
          then showvart srt
          else if external
          then fullty srt
          else srt

      fun typeofViewValence (ana : ana) srt (boundsrts, res) =
          let
            val res' =
                if #mutualwith ana srt res
                then tyvar res
                else (if external then fullty res else res)
          in
            if null boundsrts
            then res'
            else
              "("
              ^ String.concatWith " * "
                  (map (typeofBound ana) boundsrts @ [res'])
              ^ ")"
          end

      fun typeofViewConstructor (ana : ana) srt prelude arity =
          String.concat
            (transFirst
               (fn () => [])
               (fn (prelude, arg) => [prelude ^ arg])
               (" of ", " * ")
               (map (typeofViewValence ana srt) arity))

      datatype arm = Var | Oper of string

      fun emitarm pre post Var =
          emit [pre ^ "Var of " ^ showvart srt ^ post]
        | emitarm pre post (Oper oper) =
          emit [pre
                ^ oper
                ^ typeofViewConstructor ana srt pre (#arity ana srt oper)
                ^ post]

      val pre = if external then "(* datatype" else "datatype"
      val post = if external then " *)" else ""
      val fst = if external then " *  = " else " = "
      val nxt = if external then " *  | " else " | "
    in
      (*emit [pre ^ (*???*)String.concat (tyvarsofView ana srt "") ^ " " ^ shortview srt]
      >> *)appSuper
           (fn () => emit [fst ^ voidcons srt ^ " of " ^ shortview srt])
           (emitarm fst post)
           (emitarm fst "",
            emitarm nxt "",
            (fn arm => emitarm nxt "" arm >> emit [post]))
           ((if #binds ana srt srt then [Var] else [])
            @ (map Oper (#opers ana srt)))
    end

end
