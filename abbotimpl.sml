(* Abbot: implementating abstract binding trees (___.abt.impl.sml) *)

structure AbbotImpl =
struct

open Util
infixr 0 >>
open Analysis
open AbbotCore
open AbstractSML

(* Symbols and variables: effectively the same implementation *)
fun emitgenstruct issym srt =
    let
      val maybevar = if issym then "" else "Var"
      val typ = srt ^ maybevar
      val cons = if issym then "Sym" else "Var"
    in
      emit ["structure " ^ Big srt ^ maybevar ^ " =", "struct"]
      >> incr ()
      >> emit ["datatype " ^ typ ^ " = " ^ cons ^ " of string * int"]
      >> emit ["type t = " ^ srt ^ maybevar]
      >> emit ["val counter = ref 0"]
      >> emit ["val default = (\"default\", 0)"]
      >> emit ["fun hash (" ^ cons ^ " (_, id)) = id"]
      >> emit ["fun new" ^ (if issym then "sym" else "var") ^ " s"
               ^ " = " ^ cons ^ " (s, (counter := !counter + 1; !counter))"]
      >> emit ["fun equal (" ^ cons ^ " (_, x), " ^ cons ^ " (_, y)) = x = y"]
      >> emit ["fun compare (" ^ cons ^ " (_, x), " ^ cons
               ^ " (_, y)) = Int.compare (x, y)"]
      >> emit ["fun toString (" ^ cons
               ^ " (s, id)) = s ^ \"@\" ^ Int.toString id"]
      >> emit ["fun toUserString (" ^ cons ^ " (s, id)) = s"]
      >> decr ()
      >> emit ["end"]
      >> (if issym
          then emit ["type " ^ srt ^ " = " ^ Big srt ^ ".t", ""]
          else emit ["type " ^ srt ^ "Var = "  ^ Big srt ^ "Var.t", ""])
    end

fun create_view_datatype_defn ana srt =
    let
      val args = List.map (fn srt => "'" ^ srt) (#mutual ana srt)

      val oper_branches =
          List.map
            (fn oper => (oper, aritys_to_type ana srt oper false))
            (#opers ana srt)

      val body =
          if List.exists (fn x => x = srt) (#varin ana srt)
          then ("Var", SOME (TypeVar (srt ^ "Var"))) :: oper_branches
          else oper_branches
    in
      DatatypeDefn ("view", args, body)
    end

val emitsymbolstruct = emitgenstruct true
val emitvariablestruct = emitgenstruct false
fun emitimplview (ana : ana) srt =
    Emit.emit
      [TLStructure
         (Big srt,
          NONE,
          StructBody [create_view_datatype_defn ana srt])]

(* Actual implementation of sorts *)
(* Naive implementation of locally nameless *)
fun implconstructor srt oper = "Impl_" ^ Big srt ^ "_" ^ oper
fun implbvar srt = "Impl_" ^ Big srt ^ "_BoundVar"
fun implfvar srt = "Impl_" ^ Big srt ^ "_Var"
fun implfold srt = "Impl_" ^ Big srt

fun viewconstructor srt oper =
    "(into_" ^ srt ^ " o " ^ Big srt ^ "." ^ oper ^ ")"
fun viewdestructor srt oper = Big srt ^ "." ^ oper
fun viewvar srt = Big srt ^ ".Var"

fun emitdatatypeimpl_naive (ana : ana) (pre, srt) =
    let
      fun typeofFinal res =
          if #issrt ana res
          then res
          else res ^ " maybe_symbol"

      fun typeofValence srt (boundsrts, res) =
          if null boundsrts
          then typeofFinal res
          else
            "("
            ^ String.concatWith " * "
                (map (fn _ => "string") boundsrts
                 @ [typeofFinal res])
            ^ ")"

      fun typeofConstructor (ana : ana) srt arity =
          String.concat
            (transFirst
               (fn () => [])
               (fn (prelude, arg) => [prelude ^ arg])
               (" of ", " * ")
               (map (typeofValence srt) arity))

      fun emitarm ana (pre, NONE) =
          emit [pre ^ implbvar srt ^ " of IntInf.int"]
        | emitarm ana (pre, SOME NONE) =
          emit [pre ^ implfvar srt ^ " of " ^ internalvart srt]
        | emitarm ana (pre, SOME (SOME oper)) =
          emit [pre ^ implconstructor srt oper
                ^ typeofConstructor ana srt (#arity ana srt oper)]
    in
      emit [pre ^ " " ^ srt]
      >> appFirst
           (fn _ => raise Fail "Unimplemented: empty sorts")
           (emitarm ana)
           (" = "," | ")
           ((if #binds ana srt srt then [NONE, SOME NONE] else [])
            @ map (SOME o SOME) (#opers ana srt))
      >> emit [""]
    end

fun tuple [] = raise Fail "Invariant"
  | tuple [x] = x
  | tuple xs = "(" ^ String.concatWith ", " xs ^ ")"

(* Format an annotated arity correctly for application to an operator *)
fun operargs [] = ""
  | operargs [(boundsrts, srt)] =
    " " ^ tuple (map (fn (x, y) => x) (boundsrts @ [srt]))
  | operargs valences =
    " ("
    ^ String.concatWith ", "
        (map (fn (boundsrts, srt) =>
                 tuple (map #1 (boundsrts @ [srt])))
             valences)
    ^ ")"

fun emitcasefunction (ana : ana) srt
                     pre name args incase
                     bvarfn varfn operfn =
    let
      val knowsRep = isSome bvarfn

      fun annotatevalence n ([], srt) =
          (n + 1, ([], (srt ^ Int.toString n, srt)))
        | annotatevalence n (boundsrt :: boundsrts, srt) =
          let
            val (n', (anno_boundsrts, anno_srt)) =
                annotatevalence (n + 1) (boundsrts, srt)
          in
            (n',
             ((boundsrt ^ Int.toString n, boundsrt) :: anno_boundsrts,
              anno_srt))
          end

      fun annotatearity n [] = []
        | annotatearity n (valence :: valences) =
          let val (n', anno_valence) = annotatevalence n valence
          in anno_valence :: annotatearity n' valences
          end

      val opers = #opers ana srt
      val operarities =
          map (fn oper => (oper, annotatearity 1 (#arity ana srt oper))) opers
    in
      emit [pre ^ " " ^ name ^ " " ^ args ^ " ="]
      >> incr ()
      >> emit ["case " ^ incase ^ " of"]
      >> appFirst (fn _ => raise Fail "Invariant")
                  (fn (pre, (oper, arity)) =>
                      (emit [pre
                             ^ (if knowsRep
                                then implconstructor srt oper
                                else viewdestructor srt oper)
                             ^ operargs arity ^ " =>"]
                       >> incr ()
                       >> operfn (oper, arity, srt)
                       >> decr ()))
                  ("   ", " | ")
                  operarities
      >> (if not (#binds ana srt srt)
          then ()
          else if knowsRep
          then
            emit [" | " ^ implfvar srt ^ " x1 =>"]
            >> incr () >> varfn ("x1", srt) >> decr ()
            >> emit [" | " ^ implbvar srt ^ " n1 =>"]
            >> incr () >> (valOf bvarfn) ("n1", srt) >> decr ()
          else
            emit [" | " ^ viewvar srt ^ " x1 =>"]
            >> incr () >> varfn ("x1", srt) >> decr ())
      >> decr ()
      >> emit [""]
    end

fun emitcasefunctions (ana : ana) srts
                      namefn args incase
                      bvarfn varfn operfn =
    appFirst
      (fn _ => raise Fail "Zero things to emit")
      (fn (pre, srt) =>
          emitcasefunction
            ana srt pre (namefn srt) args (incase srt)
            bvarfn varfn operfn)
      ("fun", "and")
      srts


fun emitout_case (ana: ana) (oper, arity, srt) =
    let
      fun newthing boundsrt =
          if #issym ana boundsrt
          then Big boundsrt ^ ".newsym "
          else internalvar boundsrt ^ ".newvar "

      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_arity_bound ([], _) = ()
        | process_arity_bound ((boundsrtvar, boundsrt) :: valences,
                               (srtvar, srt)) =
          forcelet ()
          >> emit ["val " ^ boundsrtvar ^ " = "
                   ^ newthing boundsrt ^ boundsrtvar]
          >> emit ["val " ^ srtvar ^ " = unbind_" ^ boundsrt ^ "_" ^ srt
                   ^ " " ^ Int.toString (length valences) ^ " " ^ boundsrtvar
                   ^ " " ^ srtvar]
          >> process_arity_bound (valences, (srtvar, srt))

      fun process_arity_sym (_, (srtvar, srt)) =
          if #issym ana srt
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = out_" ^ srt ^ " " ^ srtvar]
          else ()
    in
      app process_arity_bound arity
      >> app process_arity_sym arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit [viewdestructor srt oper ^ operargs arity]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun emitinto_case (ana : ana) (oper, arity, srt) =
    let
      fun freename boundsrt =
          if #issym ana boundsrt
          then Big boundsrt ^ ".toUserString "
          else internalvar boundsrt ^ ".toUserString "

      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_arity_bound ([], _) = ()
        | process_arity_bound ((boundsrtvar, boundsrt) :: valences,
                               (srtvar, srt)) =
          forcelet ()
          >> emit ["val " ^ srtvar ^ " = bind_" ^ boundsrt ^ "_" ^ srt
                   ^ " " ^ Int.toString (length valences) ^ " " ^ boundsrtvar
                   ^ " " ^ srtvar]
          >> emit ["val " ^ boundsrtvar ^ " = "
                   ^ freename boundsrt ^ boundsrtvar]
          >> process_arity_bound (valences, (srtvar, srt))

      fun process_arity_sym (_, (srtvar, srt)) =
          if #issym ana srt
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = into_" ^ srt ^ " " ^ srtvar]
          else ()
    in
      app process_arity_bound arity
      >> app process_arity_sym arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit [implconstructor srt oper ^ operargs arity]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun emitsubst_case (ana : ana) boundsrt (oper, arity, srt) =
    let
      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_valence (_, (srtvar, srt)) =
          if #binds ana srt boundsrt
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = subst_" ^ boundsrt ^ "_" ^ srt
                     ^ " t x " ^ srtvar]
          else ()
    in
      app process_valence arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit ["into_" ^ srt ^ " ("
               ^ viewdestructor srt oper ^ operargs arity ^ ")"]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun add x 0 = x
  | add x n = "(" ^ x ^ "+" ^ Int.toString n ^ ")"

fun emitunbind_case (ana : ana) boundsrt (oper, arity, srt) =
    let
      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_arity (boundsrts, (srtvar, srt)) =
          if #binds ana srt boundsrt
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = unbind_" ^ boundsrt ^ "_" ^ srt ^ " "
                     ^ add "n" (length boundsrts) ^ " newfree " ^ srtvar]
          else ()
    in
      app process_arity arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit [implconstructor srt oper ^ operargs arity]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun emitfmap_case (ana : ana) (oper, arity, srt) =
    let
      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_valence (_, (srtvar, srt')) =
          if #mutualwith ana srt srt'
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = f_" ^ srt' ^ " " ^ srtvar]
          else ()
    in
      app process_valence arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit [viewdestructor srt oper ^ operargs arity]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun emitbind_case (ana : ana) boundsrt (oper, arity, srt) =
    let
      val needslet = ref false
      fun forcelet () =
          if !needslet then () else emit ["let"] >> incr () >> needslet := true

      fun process_arity (boundsrts, (srtvar, srt)) =
          if #binds ana srt boundsrt
          then
            forcelet ()
            >> emit ["val " ^ srtvar ^ " = bind_" ^ boundsrt ^ "_" ^ srt ^ " "
                     ^ add "n" (length boundsrts) ^" oldfree " ^ srtvar]
          else ()
    in
      app process_arity arity
      >> (if !needslet then decr () >> emit ["in"] >> incr () else ())
      >> emit [implconstructor srt oper ^ operargs arity]
      >> (if !needslet then decr () >> emit ["end"] else ())
    end

fun emittoString_case (ana : ana) (oper, arity, srt) =
    let
      fun process_valence ([], (srtvar, srt)) =
          (if #issym ana srt
           then Big srt ^ ".toString"
           else "toString_" ^ srt)
          ^ " " ^ srtvar
        | process_valence ((boundsrtvar, boundsrt) :: valence, srt) =
          (if #issym ana boundsrt
           then Big boundsrt
           else internalvar boundsrt)
          ^ ".toString " ^ boundsrtvar
          ^ "^\".\"^" ^ process_valence (valence, srt)
    in
      if null arity
      then emit ["\"" ^ oper ^ "\""]
      else emit ["\"" ^ oper ^ "(\"^"
                 ^ String.concatWith "^\", \"^" (map process_valence arity)
                 ^ "^\")\""]
    end

fun emitaequiv (ana : ana) (pre, srt) =
    let
      val opers = #opers ana srt

      fun handlearity n [] = raise Fail "Invariant"
        | handlearity n ((boundvars, srt) :: xs) =
          let val n' = Int.toString n
              val m' = Int.toString (length boundvars + 1)
              val callargs =
                  if null boundvars
                  then "(#" ^ n' ^ " x, #" ^ n' ^ " y)"
                  else
                    "(#" ^ m' ^ " (#" ^ n' ^ " x), #" ^ m' ^ " (#" ^ n' ^ " y))"
          in
            emit ["aequiv_" ^ srt ^ " " ^ callargs
                  ^ (if null xs then "" else " andalso")]
            >> (if null xs then () else handlearity (n + 1) xs)
          end

      fun handleoper (pre, oper) =
          let val args = #arity ana srt oper
          in case args of
                 [] =>
                 emit [pre ^ "(" ^ implconstructor srt oper ^ ", "
                       ^ implconstructor srt oper ^ ") => true"]
               | [([], srt')] =>
                 emit [pre ^ "(" ^ implconstructor srt oper ^ " x, "
                       ^ implconstructor srt oper ^ " y) => aequiv_"
                       ^ srt' ^ " (x, y)"]
               | [(_, srt')] =>
                 emit [pre ^ "(" ^ implconstructor srt' oper ^ " x, "
                       ^ implconstructor srt oper ^ " y) => aequiv_"
                       ^ srt' ^ " (#2 x, #2 y)"]
               | _ =>
                 emit [pre ^ "(" ^ implconstructor srt oper ^ " x, "
                       ^ implconstructor srt oper ^ " y) =>"]
                 >> incr ()
                 >> handlearity 1 args
                 >> decr ()
          end
    in
      emit [pre ^ " aequiv_" ^ srt ^ " (x, y) ="]
      >> incr ()
      >> emit ["case (x, y) of"]
      >> appFirst
           (fn _ => raise Fail "Invariant")
           handleoper
           ("   ", " | ")
           opers
      >> (if #binds ana srt srt
          then
            emit [" | (" ^ implbvar srt ^ " x, "
                  ^ implbvar srt ^ " y) => x = y"]
            >> emit [" | (" ^ implfvar srt ^ " x, " ^ implfvar srt ^ " y) => "
                     ^ internalvar srt ^ ".equal (x, y)"]
          else ())
      >> emit [" | _ => false",""]
      >> decr ()
    end

(* Emit a mutually-interdependent block of implementations *)
fun emitblockimpl (ana : ana) srts =
    let
      (* Takes advantage of the fact that 'varin' has to be the same across
       * a block of mutually-defined sorts *)
      val varsinthese = #varin ana (hd srts)
      val symsinthese = #symin ana (hd srts)
      val dummy = " = fn _ => raise Fail \"Unimpl\""
    in
      emit ["(* Implementation of recursive block: "
            ^ String.concatWith ", " srts ^ " *)",
            ""]
      >> app (emitimplview ana) srts
      >> emit ["(* Naive and minimal implementation *)"]
      >> emit ["local"]
      >> incr ()
      >> appFirst
           (fn _ => raise Fail "Invariant")
           (emitdatatypeimpl_naive ana)
           ("datatype", "and")
           srts
      >> decr ()
      >> emit ["in"]
      >> incr ()
      >> app (fn srt => emit ["type " ^ srt ^ " = " ^ srt]) srts
      >> emit [""]

      (* Learn to unbind all the variables that are bound in these sorts *)
      >> app (fn boundsrt =>
                 emitcasefunctions
                   ana srts (fn srt => "unbind_" ^ boundsrt ^ "_" ^ srt)
                   ("n newfree x") (fn _ => "x")
                   (SOME (fn (n', srt) =>
                             if #issym ana srt orelse boundsrt <> srt
                             then emit ["x"]
                             else emit ["if " ^ n' ^ " < n then x",
                                        "else " ^ implfvar srt ^ " newfree"]))
                   (fn _ => emit ["x"])
                   (emitunbind_case ana boundsrt))
           (varsinthese @ symsinthese)

      (* Use unbind to implement projection type -> view *)
      >> emitcasefunctions
           ana srts (fn srt => "out_" ^ srt) "x" (fn _ => "x")
           (SOME (fn _ => emit ["raise Fail \"Invariant: exposed bvar\""]))
           (fn (v, srt) => emit [viewvar srt ^ " " ^ v])
           (emitout_case ana)

      (* Learn to bind all the variables that are bound in these sorts *)
      >> app (fn boundsrt =>
                 emitcasefunctions
                   ana srts (fn srt => "bind_" ^ boundsrt ^ "_" ^ srt)
                   ("n oldfree x") (fn _ => "x")
                   (SOME (fn _ => emit ["x"]))
                   (fn (x, srt) =>
                       if srt <> boundsrt
                       then emit ["x"]
                       else
                         emit ["if " ^ internalvar boundsrt
                               ^ ".equal (oldfree, " ^ x ^ ") then "
                               ^ implbvar boundsrt ^ " n else x"])
                   (emitbind_case ana boundsrt))
           (varsinthese @ symsinthese)

      (* Use bind to implement injection view -> type *)
      >> emitcasefunctions
           ana srts (fn srt => "into_" ^ srt) "x" (fn _ => "x") NONE
           (fn (x, srt) => emit [implfvar srt ^ " " ^ x])
           (emitinto_case ana)

      (* Alpha-equivalence is a simultaneous traversal;
       * emitcasefunctions isn't really appropriate *)
      >> appFirst (fn _ => raise Fail "Invariant")
           (emitaequiv ana) ("fun", "and") srts

      >> app (fn varsrt =>
                 app (fn srt => emit ["val free_" ^ varsrt ^ "_" ^ srt ^ dummy])
                     srts)
           (#varin ana (hd srts))
      >> app (fn symsrt =>
                 app (fn srt => emit ["val free_" ^ symsrt ^ "_" ^ srt ^ dummy])
                     srts)
           (#symin ana (hd srts))
      >> decr ()
      >> emit ["end","","(* Derived functions *)"]
      >> app (fn boundsrt =>
                 emitcasefunctions
                   ana srts (fn srt => "subst_" ^ boundsrt ^ "_" ^ srt) "t x s"
                   (fn srt => "out_" ^ srt ^ " s") NONE
                   (fn (x, srt) =>
                       if srt <> boundsrt
                       then emit ["s"]
                       else
                         emit
                           ["if " ^ internalvar srt ^ ".equal (x, " ^ x ^ ")",
                            "then t else s"])
                   (emitsubst_case ana boundsrt))
           varsinthese

      >> emitcasefunctions
           ana srts (fn srt => "toString_" ^ srt) "x"
           (fn srt => "out_" ^ srt ^ " x") NONE
           (fn (x, srt) => emit [internalvar srt ^ ".toString " ^ x])
           (emittoString_case ana)

      >> emit [""]
    end

(* We want to put this in the abt.impl.sml file in order to have
 * the user structure simply ascribe to an existing signature *)
fun emitfinalimpl (ana : ana) srt =
    emit ["structure " ^ Big srt ^ " =", "struct"]
    >> incr ()
    >> emit ["type t = " ^ srt]
    >> app (fn s' => emit ["type " ^ s' ^ " = " ^ s']) (#mutual ana srt)
    >> app (fn s' => if (#binds ana srt s')
                     then emit ["type " ^ s' ^ "Var = " ^ internalvart s']
                     else ())
         (#mutual ana srt)
    >> emit ["open " ^ Big srt]
    >> emit [""]
    >> emitcasefunction
         ana srt "fun" "map"
         (String.concatWith " "
                            (map (fn s => "f_" ^ s) (#mutual ana srt)) ^ " x")
         "x" NONE (fn (x, _) => emit [viewvar srt ^ " " ^ x])
         (emitfmap_case ana)
    >> emit ["val into = into_" ^ srt]
    >> emit ["val out = out_" ^ srt]
    >> (if #binds ana srt srt
        then emit ["structure Var = " ^ internalvar srt,
                   "val Var' = fn x => into (Var x)"]
        else ())
    >> emit ["val aequiv = aequiv_" ^ srt]
    >> emit ["val toString = toString_" ^ srt]
    >> app (fn s' => emit ["val subst" ^ (if srt <> s' then Big s' else "")
                           ^ " = subst_" ^ s' ^ "_" ^ srt])
         (#varin ana srt)
    >> app (fn s' => emit ["val free" ^ (if srt <> s' then (Big s' ^ "V") else "v")
                           ^ "ars = free_" ^ s' ^ "_" ^ srt])
         (#varin ana srt)
    >> app (fn s' => emit ["val free" ^ Big s' ^ " = free_" ^ s' ^ "_" ^ srt])
         (#symin ana srt)
    >> app (fn oper =>
               if null (#arity ana srt oper)
               then emit ["val " ^ oper ^ "' = into " ^ viewdestructor srt oper]
               else emit ["val " ^ oper ^ "' = fn x => into (" ^ oper ^ " x)"])
         (#opers ana srt)
    >> decr ()
    >> emit ["end", ""]

fun doit_impl (ana : ana) =
    emit ["structure AbbotImpl =", "struct"]
    >> incr ()
    >> emit ["(* All symbols *)"]
    >> app emitsymbolstruct (#symbs ana)
    >> emit ["datatype 'a maybe_symbol",
             " = bound_symbol of IntInf.int",
             " | free_symbol of 'a",
             ""]
    >> app (fn srt =>
               emit ["fun unbind_" ^ srt ^ "_" ^ srt ^ " n newfree x ="]
               >> emit ["    case x of"]
               >> emit ["       free_symbol _ => x"]
               >> emit ["     | bound_symbol m =>"]
               >> emit ["       if m < n then x else free_symbol newfree"]
               >> emit [""]
               >> emit ["fun bind_" ^ srt ^ "_" ^ srt ^ " n oldfree x ="]
               >> emit ["    case x of"]
               >> emit ["       free_symbol freesym =>"]
               >> emit ["       if " ^ Big srt ^ ".equal (oldfree, freesym)"]
               >> emit ["       then bound_symbol n else x"]
               >> emit ["     | bound_symbol _ => x"]
               >> emit [""]
               >> emit ["fun out_" ^ srt ^ " (bound_symbol _) ="]
               >> emit ["    raise Fail \"Invariant: exposed bvar\""]
               >> emit ["  | out_" ^ srt ^ " (free_symbol x) = x"]
               >> emit [""]
               >> emit ["fun into_" ^ srt ^ " x = free_symbol x"]
               >> emit [""]
               >> emit ["fun aequiv_" ^ srt ^ " (x, y) ="]
               >> emit ["   case (x, y) of"]
               >> emit ["      (free_symbol x, free_symbol y) => " ^ Big srt
                        ^ ".equal (x, y)"]
               >> emit ["    | (bound_symbol x, bound_symbol y) => x = y"]
               >> emit ["    | _ => false", ""])
         (#symbs ana)
    >> emit ["(* All variables *)"]
    >> app emitvariablestruct
         (List.filter
            (fn srt => #binds ana srt srt)
            (List.concat (#sorts ana)))
    >> app (emitblockimpl ana) (#sorts ana)
    >> emit ["(* Rebind structs with full contents *)"]
    >> app (emitfinalimpl ana) (List.concat (#sorts ana))
    >> decr ()
    >> emit ["end"]

end
