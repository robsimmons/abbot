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
          [("t", TypeDecl ([], SOME tyvar)),
           ("new", ValDecl (Arrow (TypeVar "string", tyvar))),
           ("equal",
            ValDecl (Arrow (Prod [tyvar, tyvar], TypeVar "bool"))),
           ("compare", ValDecl (Arrow(Prod [tyvar, tyvar], TypeVar "order"))),
           ("toString", ValDecl (Arrow (tyvar, TypeVar "string"))),
           ("hash", ValDecl (Arrow (tyvar, TypeVar "int")))]
    in
      (if is_var
       then "Var"
       else Big sym,
       StructureDecl
         (SigBody
            (if is_var
             then gen_decls
             else (sym, TypeDecl ([], NONE)) :: gen_decls)))
    end

fun create_view_datatype_decl ana mutual srt =
    let
      val args = List.map (fn srt => "'" ^ srt) mutual

      val body =
          List.map
            (fn oper => (oper, aritys_to_type ana srt oper))
            (#opers ana srt)
    in
      ("view", DatatypeDecl (args, body))
    end

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

      val var_structure_decl =
          if List.exists (fn x => x = srt) (#varin ana srt)
          then [create_gen_structure_decl true srt]
          else []

      val convenient_contructors =
          List.map
            (fn oper =>
                (oper ^ "'",
                 ValDecl
                   (case aritys_to_type ana srt oper of
                        NONE => TypeVar srt
                      | SOME TYPE => Arrow (TYPE, TypeVar srt))))
            (if List.exists (fn x => x = srt) (#varin ana srt)
             then ("Var", [srt ^ "var"]) :: #opers ana srt
             else #opers ana srt)

      val map_type =
          List.foldr
            Arrow
            (Arrow (polymorphic_view ana srt "1", polymorphic_view ana srt "2"))
            (List.map
               (fn srt =>
                   Arrow (TypeVar ("'" ^ srt ^ "1"), TypeVar ("'" ^ srt ^ "2")))
               mutual)

      val substitutions =
          List.map
            (fn srt' =>
                (if srt = srt'
                 then "subst"
                 else "subst" ^ Big srt',
                 ValDecl
                   (Arrow
                      (TypeVar srt',
                       Arrow
                         (TypeVar (srt' ^ "Var"),
                          Arrow (TypeVar srt, TypeVar srt))))))
            (#varin ana srt)

      val all_decls =
          List.concat
            [mutual_type_decls,
             [("t", TypeDecl ([], SOME (TypeVar srt)))],
             mutual_var_decls,
             var_structure_decl,
             [create_view_datatype_decl ana mutual srt],
             convenient_contructors,
             [("into", ValDecl (Arrow (concrete_view ana srt, TypeVar srt))),
              ("out", ValDecl (Arrow (TypeVar srt, concrete_view ana srt))),
              ("aequiv", ValDecl (Arrow (Prod [TypeVar srt, TypeVar srt], TypeVar "bool"))),
              ("toString", ValDecl (Arrow (TypeVar srt, TypeVar "string"))),
              ("map", ValDecl map_type)],
             substitutions]
    in
      (Big srt, StructureDecl (SigBody all_decls))
    end

fun create_sharing_decls mods srt =
    case mods of
        [x] => []
      | x::y::mods' =>
        ("",
         SharingDecl
           (ModProj (Big x, TypeVar srt), ModProj (Big y, TypeVar srt)))
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
      val symbols = List.map (create_gen_structure_decl false) (#symbs ana)
      val sorts =
          List.concat
            (List.map (create_mutual_sort_structure_decls ana) (#sorts ana))
    in
      Emit.emit [("ABBOT", TLSignature (SigBody (symbols @ sorts)))]
    end
end
