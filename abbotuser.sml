(* Abbot: emitting user interface (___.abt.sig) *)

structure AbbotUser =
struct

open Analysis
open AbstractSML
open AbbotCore

fun create_gen_structure_decl is_var sym =
    let
      val tyvar =
          if is_var
          then TypeVar (sym ^ "Var")
          else TypeVar sym

      val gen_decls =
          [TypeDecl ("t", [], SOME tyvar),
           ValDecl
             ("new" ^ (if is_var then "var" else "sym"),
              Arrow (TypeVar "string", tyvar)),
           ValDecl
             ("equal",
              Arrow (Prod [tyvar, tyvar], TypeVar "bool")),
           ValDecl ("compare", Arrow (Prod [tyvar, tyvar], TypeVar "order")),
           ValDecl ("toString", Arrow (tyvar, TypeVar "string")),
           ValDecl ("hash", Arrow (tyvar, TypeVar "int"))]
    in
      StructureDecl
        (if is_var
         then "Var"
         else Big sym,
         SigBody
           (if is_var
            then gen_decls
            else (TypeDecl (sym, [], NONE)) :: gen_decls))
    end

fun create_view_datatype_decl ana srt =
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
      DatatypeDecl ("view", args, body)
    end

fun create_sort_structure_decl (ana : ana) srt =
    let
      val mutual_type_decls =
          List.map (fn srt => TypeDecl (srt, [], NONE)) (#mutual ana srt)

      val mutual_var_decls =
          List.concat
            (List.map
               (fn var_srt =>
                   if #mutualwith ana srt var_srt
                   then [TypeDecl (var_srt ^ "Var", [], NONE)]
                   else [])
               (#varin ana srt))

      val var_structure_decl =
          if List.exists (fn x => x = srt) (#varin ana srt)
          then [create_gen_structure_decl true srt]
          else []

      val convenient_contructors =
          let
            val oper_constructors =
                List.map
                  (fn oper =>
                      ValDecl
                        (oper ^ "'",
                         case aritys_to_type ana srt oper true of
                             NONE => TypeVar srt
                           | SOME TYPE => Arrow (TYPE, TypeVar srt)))
                  (#opers ana srt)
          in
            if List.exists (fn x => x = srt) (#varin ana srt)
            then
              ValDecl ("Var'", Arrow (TypeVar (srt ^ "Var"), TypeVar srt))
              :: oper_constructors
            else oper_constructors
          end

      val map_type =
          List.foldr
            Arrow
            (Arrow (polymorphic_view ana srt "1", polymorphic_view ana srt "2"))
            (List.map
               (fn srt =>
                   Arrow (TypeVar ("'" ^ srt ^ "1"), TypeVar ("'" ^ srt ^ "2")))
               (#mutual ana srt))

      val substitutions =
          List.map
            (fn srt' =>
                ValDecl
                  (if srt = srt'
                   then "subst"
                   else "subst" ^ Big srt',
                   Arrow
                     (TypeVar srt',
                      Arrow
                        (TypeVar (srt' ^ "Var"),
                         Arrow (TypeVar srt, TypeVar srt)))))
            (#varin ana srt)

      val all_decls =
          List.concat
            [mutual_type_decls,
             [TypeDecl ("t", [], SOME (TypeVar srt))],
             mutual_var_decls,
             var_structure_decl,
             [create_view_datatype_decl ana srt],
             convenient_contructors,
             [ValDecl ("into", Arrow (concrete_view ana srt, TypeVar srt)),
              ValDecl ("out", Arrow (TypeVar srt, concrete_view ana srt)),
              ValDecl ("aequiv", Arrow (Prod [TypeVar srt, TypeVar srt], TypeVar "bool")),
              ValDecl ("toString", Arrow (TypeVar srt, TypeVar "string")),
              ValDecl ("map", map_type)],
             substitutions]
    in
      StructureDecl (Big srt, SigBody all_decls)
    end

fun create_sharing_decls mods srt =
    case mods of
        [x] => []
      | x::y::mods' =>
        SharingDecl (ModProj (Big x, TypeVar srt), ModProj (Big y, TypeVar srt))
        :: create_sharing_decls (y::mods') srt

fun create_mutual_sort_structure_decls ana srts =
    let
      val sort_structures = List.map (create_sort_structure_decl ana) srts
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
      val symbols = List.map (create_gen_structure_decl false) (#symbs ana)
      val sorts =
          List.concat
            (List.map (create_mutual_sort_structure_decls ana) (#sorts ana))
    in
      Emit.emit [TLSignature ("ABBOT", SigBody (symbols @ sorts))]
    end
end
