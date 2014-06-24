(* Abbot: emitting user interface (___.abt.user.sml) *)

structure AbbotUser =
struct

open Analysis
open AbstractSML
open AbbotCore
(*
(* Symbols and variables: basically the same thing *)
fun emitgensig issym srt =
    let
      val maybevar = if issym then "" else "Var"
      val typ = srt ^ maybevar
    in
      emit ["signature "
            ^ BIG srt
            ^ (if issym then "" else "_VAR")
            ^ " =", "sig"]
      >> incr ()
      >> emit ["type "
               ^ typ
               ^ (if issym
                  then (" = AbbotImpl."^Big srt^maybevar^"."^typ)
                  else "")]
      >> emit ["type t = " ^ typ]
      >> emit ["val new"
               ^ (if issym then "sym" else "var")
               ^ " : string -> "
               ^ typ]
      >> emit ["val equal : (" ^ typ ^ " * " ^ typ ^ ") -> bool"]
      >> emit ["val compare : (" ^ typ ^ " * " ^ typ ^ ") -> order"]
      >> emit ["val toString : " ^ typ ^ " -> string"]
      >> emit ["val hash : " ^ typ ^ " -> int"]
      >> decr ()
      >> emit ["end"]
    end

val emitsymbolsig = emitgensig true
val emitvariablesig = emitgensig false

fun emituservariables (ana : ana) =
    let
      val mkvars =
          List.filter
            (fn srt => #binds ana srt srt)
            (List.concat (#sorts ana))
    in
      if null mkvars
      then ()
      else
        emit ["(* Signatures for variables *)", ""]
        >> app (fn srt => emitvariablesig srt >> emit [""]) mkvars
    end

fun emitusersymbols (ana : ana) =
    if null (#symbs ana)
    then ()
    else
      emit ["(* Implementation of symbol sorts *)",""]
      >> app (fn srt =>
                 (emitsymbolsig srt
                  >> emit
                       ["structure "
                        ^ Big srt
                        ^ " :> "
                        ^ BIG srt
                        ^ " = AbbotImpl."
                        ^ Big srt,
                        ""]))
           (#symbs ana)

(* Sorts and variable sorts to strings *)
fun ss (ana : ana) srt s' =
    if #mutualwith ana srt s'
    then s'
    else Big s' ^ "." ^ s'
fun ssv (ana : ana) srt varsrt =
    if #mutualwith ana srt varsrt
    then varsrt ^ "Var"
    else Big varsrt ^ ".Var." ^ varsrt ^ "Var"

(* The convienece constructors *)
fun emitconvienenceconstructor (ana : ana) srt oper =
    let
      fun typeofBound boundsrt =
          if #issrt ana boundsrt
          then ssv ana srt boundsrt (* Variable *)
          else ss ana srt boundsrt (* Symbol *)
      fun typeofValence (boundsrts, res) =
          if null boundsrts then ss ana srt res
          else
            "("
            ^ String.concatWith " * "
                (map typeofBound boundsrts @ [ss ana srt res])
            ^ ")"

      val args = map typeofValence (#arity ana srt oper)
    in
      if null args
      then emit ["val " ^ oper ^ "' : " ^ srt]
      else
        emit
          ["val " ^ oper ^ "' : "
           ^ String.concatWith " * " args
           ^ " -> " ^ srt]
    end

(* The sealing for the user struct is the most interesting part... *)
fun emituserstruct (ana : ana) srt =
    let
      fun emitwhereclauses s' =
          if #binds ana srt s'
          then
            emit ["where type " ^ s' ^ " = AbbotImpl." ^ s']
            >> emit ["where type " ^ s' ^ "Var "
                     ^ "= AbbotImpl." ^ Big s' ^ "Var." ^ s' ^ "Var"]
          else emit ["where type " ^ s' ^ " = AbbotImpl." ^ s']
    in
      emit ["signature " ^ BIG srt ^ " =","sig"]
      >> incr ()
      >> app (fn s' =>
                 emit ["type " ^ s' ^ " (* = " ^ fullty s' ^ " *)"]
                 >> (if (#binds ana srt s')
                     then
                       emit
                         ["type " ^ s' ^ "Var (* = " ^ externalvart s' ^ " *)"]
                     else ()))
           (#mutual ana srt)
      >> emit ["type t = " ^ srt, ""]

      >> (if (#binds ana srt srt)
          then emit ["structure Var : "
                     ^ BIG srt
                     ^ "_VAR where type "
                     ^ srt
                     ^ "Var = "
                     ^ srt
                     ^ "Var"]
          else ())
      >> emit ["datatype " ^ shortview srt
               ^ " = datatype AbbotImpl." ^ Big srt ^ "." ^ shortview srt]
      >> emitview ana true srt
      >> emit [""]
      >> (if #binds ana srt srt
          then emit ["val Var' : "^srt^"Var -> "^srt]
          else ())
      >> app (emitconvienenceconstructor ana srt) (#opers ana srt)
      >> emit [""]

      >> emit ["val into :"
               ^ concretesofView ana srt
               ^ " "
               ^ shortview srt
               ^ " -> "
               ^ srt]
      >> emit ["val out : " ^ srt ^ " ->"
               ^ concretesofView ana srt ^ " " ^ shortview srt]
      >> emit ["val aequiv : " ^ srt ^ " * " ^ srt ^ " -> bool"]
      >> emit ["val toString : " ^ srt ^ " -> string"]
      >> (if #binds ana srt srt
          then emit ["val subst : " ^ srt ^ " -> " ^ srt ^ "Var -> " ^ srt ^ " -> " ^ srt
                    (*, "val freevars : "^srt^" -> "^srt^"Var list" *)]
          else ())
      >> app (fn s' =>
                 if s' = srt
                 then ()
                 else
                   emit ["val subst" ^ Big s' ^ " : "^ ss ana srt s' ^ " -> "
                         ^ ssv ana srt s' ^ " -> "
                         ^ srt
                         ^ " -> "
                         ^ srt(*,"val free"^Big s'^"Vars : "^srt^" -> "^
                           ssv ana srt s'^" list" *)])
           (#varin ana srt)
      (* >> app (fn s' => emit ["val free" ^ Big s' ^ " : " ^ srt ^ " -> " ^ Big s' ^ "." ^ s' ^ " list"])
      (#symin ana srt)*)
      >> appFirst
           (fn () => raise Fail "Can't fmap")
           (fn (prelude, srt) =>
               emit [prelude ^"("^tyvar srt^"1 -> "^tyvar srt^"2)"])
           ("val fmap : ","       -> ")
           (#mutual ana srt)
      >> emit ["       ->"
               ^ tyvarsofView ana srt "1"
               ^ " "
               ^ shortview srt
               ^ " ->"
               ^ tyvarsofView ana srt "2"
               ^ " "
               ^ shortview srt]
      >> decr ()
      >> emit ["end", "structure " ^ Big srt ^ " : " ^ BIG srt]
      >> incr () >> incr ()
      >> app emitwhereclauses (#mutual ana srt)
      >> emit ["= AbbotImpl." ^ Big srt, ""]
      >> decr () >> decr ()
    end

fun doit_user (ana : ana) =
    emitusersymbols ana
    >> emituservariables ana
    >> emit ["(* Implementation of normal sorts *)", ""]
    >> app (emituserstruct ana) (List.concat (#sorts ana))
    >> emit ["(* Intentionally shadow internals *)"]
    >> emit ["structure AbbotImpl = struct end"]
*)
fun create_sym_structure_decl sym =
    (Big sym,
     StructureDecl
       (SigBody
          [(sym, TypeDecl ([], NONE)),
           ("t", TypeDecl ([], SOME (TypeVar sym))),
           ("new", ValDecl (Arrow (TypeVar "string", TypeVar sym))),
           ("equal",
            ValDecl (Arrow (Prod [TypeVar sym, TypeVar sym], TypeVar "bool"))),
           ("compare",
            ValDecl (Arrow(Prod [TypeVar sym, TypeVar sym], TypeVar "order"))),
           ("toString", ValDecl (Arrow (TypeVar sym, TypeVar "string"))),
           ("hash", ValDecl (Arrow (TypeVar sym, TypeVar "int")))]))

fun arity_to_type (ana : ana) srt (bound, srt') =
    let
      val srt_type =
          if #mutualwith ana srt srt'
          then TypeVar srt'
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

fun aritys_to_type ana srt oper =
    case #arity ana srt oper of
        [] => NONE
      | [a] => SOME (arity_to_type ana srt a)
      | arity => SOME (Prod (List.map (arity_to_type ana srt) arity))

fun create_sort_structure_decl (ana : ana) mutual srt =
    let
      val mutual_type_decls =
          List.map (fn srt => (srt, TypeDecl ([], NONE))) mutual

      val mutual_var_decls =
          List.concat
            (List.map
               (fn var_srt =>
                   if #mutualwith ana srt var_srt
                   then [(var_srt ^ "Var", TypeDecl ([], NONE))]
                   else [])
               (#varin ana srt))

      val map_type =
          List.foldr
            (fn (srt, acc) =>
                Arrow
                  (Arrow
                     (TypeVar ("'" ^ srt ^ "1"),
                      TypeVar ("'" ^ srt ^ "2")),
                   acc))
            (Arrow (App (tyvarsofView ana srt "1", TypeVar "view"),
                    App (tyvarsofView ana srt "2", TypeVar "view")))
            mutual
    in
      (Big srt,
       StructureDecl
         (SigBody
            (mutual_type_decls
             @ [("t", TypeDecl ([], SOME (TypeVar srt)))]
             @ mutual_var_decls
             @ [("view",
                 DatatypeDecl
                   (List.map (fn srt => "'" ^ srt) mutual,
                    List.map
                      (fn oper => (oper, aritys_to_type ana srt oper))
                      (#opers ana srt)))]
             @ List.map
                 (fn oper =>
                     (oper ^ "'",
                      ValDecl
                        (case aritys_to_type ana srt oper of
                             NONE => TypeVar srt
                           | SOME TYPE =>
                             Arrow (TYPE, TypeVar srt))))
                 (#opers ana srt)
             @ [("into",
                 ValDecl
                   (Arrow
                      (App (concretesofView ana srt, TypeVar "view"),
                       TypeVar srt))),
                ("out",
                 ValDecl
                   (Arrow
                      (TypeVar srt,
                       App (concretesofView ana srt, TypeVar "view")))),
                ("aequiv", ValDecl (Arrow (Prod [TypeVar srt, TypeVar srt], TypeVar "bool"))),
                ("toString", ValDecl (Arrow (TypeVar srt, TypeVar "string"))),
                ("map", ValDecl map_type)]
             @ [(*??? substitutions*)])))
    end

fun create_sharing_decls mods srt =
    case mods of
        [x] => []
      | x::y::mods' =>
        ("",
         SharingDecl
           (ModProj (Big x, TypeVar srt),
            ModProj (Big y, TypeVar srt)))
        :: create_sharing_decls (y::mods') srt

fun create_mutual_sort_structure_decls ana srts =
    let
      val sort_structures = List.map (create_sort_structure_decl ana srts) srts
    in
      case srts of
          ([] | [_]) => sort_structures
        | srt::_ =>
          sort_structures
          @ List.concat
              (List.map
                 (create_sharing_decls srts)
                 (srts @ List.map (fn srt => srt ^ "Var") (#varin ana srt)))
    end

fun doit_user (ana : ana) =
    let
      val symbols = List.map create_sym_structure_decl (#symbs ana)
      val sorts =
          List.concat
            (List.map (create_mutual_sort_structure_decls ana) (#sorts ana))
    in
      Emit.emit [("ABBOT", TLSignature (SigBody (symbols @ sorts)))]
    end
end
