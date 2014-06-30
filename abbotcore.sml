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

fun polymorphic_view (ana : ana) srt post =
    App
      (List.map (fn srt => TypeVar ("'" ^ srt ^ post)) (#mutual ana srt),
       TypeVar "view")

fun concrete_view (ana : ana) srt =
    App (List.map TypeVar (#mutual ana srt), TypeVar "view")

fun arity_to_type concrete (ana : ana) srt (bound, srt') =
    let
      val srt_type =
          if #mutualwith ana srt srt'
          then TypeVar ((if concrete then "" else "'") ^ srt')
          else ModProj (Big srt', TypeVar "t")
    in
      case bound of
          [] => srt_type
        | _ =>
          Prod
            (List.map
               (fn srt_or_sym =>
                   if #issym ana srt_or_sym
                   then ModProj (Big srt_or_sym, TypeVar "t")
                   else if #mutualwith ana srt srt_or_sym
                   then TypeVar (srt_or_sym ^ "Var")
                   else ModProj (Big srt_or_sym, TypeVar (srt_or_sym ^ "Var")))
               bound
             @ [srt_type])
    end

fun aritys_to_type ana srt oper concrete =
    case #arity ana srt oper of
        [] => NONE
      | [a] => SOME (arity_to_type concrete ana srt a)
      | arity => SOME (Prod (List.map (arity_to_type concrete ana srt) arity))
end
