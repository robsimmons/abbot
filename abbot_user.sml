(* Abbot: emitting user interface (___.abt.sig) *)

structure AbbotUser =
struct

open Analysis
open SMLSyntax
open AbbotCore

fun create_view_datatype_decl ana (srt, opers) =
    let
      val args = List.map (fn srt => "'" ^ sort_to_string srt) (#mutual ana srt)

      val oper_branches =
          List.map
            (fn (oper, arity_opt) =>
                (oper,
                 (case arity_opt of
                      NONE => NONE
                    | SOME arity =>
                      SOME (arity_to_type ana srt false arity))))
            opers

      val body =
          if #hasvar ana srt
          then ("Var", SOME (sort_to_var_type srt)) :: oper_branches
          else oper_branches
    in
      TypeDecls {datatypes = [("view", args, body)], aliases = []}
    end

fun create_sort_structure_decl (ana : ana) (srt, opers) =
    let
      val mutual_type_decls =
          List.map
            (fn srt =>
                TypeDecls
                  {datatypes = [],
                   aliases = [(sort_to_string srt, [], NONE)]})
            (#mutual ana srt)

      val mutual_var_decls =
          List.map
            (fn var_srt =>
                TypeDecls
                  {datatypes = [],
                   aliases = [(sort_to_string var_srt ^ "Var", [], NONE)]})
            (List.filter (#hasvar ana) (#mutual ana srt))

      val var_structure_decl =
          if #hasvar ana srt
          then
            [StructureDecl
               ("Var",
                WhereType
                  (SigVar "TEMP",
                   TypeVar "t",
                   sort_to_var_type srt))]
          else []

      val convenient_contructors =
          let
            val oper_constructors =
                List.map
                  (fn (oper, arity_opt) =>
                      ValDecl
                        (oper ^ "'",
                         case arity_opt of
                             NONE => sort_to_type true srt
                           | SOME arity =>
                             Arrow
                               (arity_to_type ana srt true arity,
                                sort_to_type true srt)))
                  opers
          in
            if #hasvar ana srt
            then
              ValDecl
                ("Var'",
                 Arrow
                   (sort_to_var_type srt,
                    sort_to_type true srt))
              :: oper_constructors
            else
              oper_constructors
          end

      val map_type =
          List.foldr
            Arrow
            (Arrow (polymorphic_view ana srt "1", polymorphic_view ana srt "2"))
            (List.map
               (fn srt =>
                   Arrow
                     (TypeVar ("'" ^ sort_to_string srt ^ "1"),
                      TypeVar ("'" ^ sort_to_string srt ^ "2")))
               (#mutual ana srt))

      val substitutions =
          List.map
            (fn srt' =>
                ValDecl
                  (if srt = srt'
                   then "subst"
                   else "subst" ^ Big (sort_to_string srt'),
                   Arrow
                     ((if #mutualwith ana srt srt'
                       then sort_to_type true srt'
                       else TypeVar (Big (sort_to_string srt') ^ ".t")),
                      Arrow
                        ((if #mutualwith ana srt srt'
                          then sort_to_var_type srt'
                          else TypeVar (Big (sort_to_string srt') ^ ".Var.t")),
                         Arrow (sort_to_type true srt, sort_to_type true srt)))))
            (List.filter (#hasvar ana) (#dependencies ana srt))

      val all_decls =
          List.concat
            [mutual_type_decls,
             [TypeDecls
                {datatypes = [],
                 aliases = [("t", [], SOME (sort_to_type true srt))]}],
             mutual_var_decls,
             [BlankDecl],
             var_structure_decl,
             [BlankDecl],
             [create_view_datatype_decl ana (srt, opers)],
             [BlankDecl],
             convenient_contructors,
             [BlankDecl,
              ValDecl
                ("into", Arrow (concrete_view ana srt, sort_to_type true srt)),
              ValDecl
                ("out", Arrow (sort_to_type true srt, concrete_view ana srt)),
              ValDecl
                ("aequiv",
                 Arrow
                   (Prod [sort_to_type true srt, sort_to_type true srt],
                    TypeVar "bool")),
              ValDecl
                ("toString", Arrow (sort_to_type true srt, TypeVar "string"))(*,
              ValDecl ("map", map_type) ??? *)],
             (case substitutions of [] => [] | _ => BlankDecl :: substitutions)]
    in
      StructureDecl (Big (sort_to_string srt), SigBody all_decls)
    end

fun create_sharing_decls mods field =
    case mods of
        [] => raise Fail "Internal Abbot Error"
      | [x] => []
      | x::y::mods' =>
        SharingDecl
          (ModProj (Big (sort_to_string x), TypeVar field),
           ModProj (Big (sort_to_string y), TypeVar field))
        :: create_sharing_decls (y::mods') field

fun create_mutual_sort_structure_decls ana srts =
    let
      val sort_structures = List.map (create_sort_structure_decl ana) srts
    in
      case srts of
          ([] | [_]) => sort_structures
        | (srt, _)::_ =>
          sort_structures
          @ List.concat
              (List.map
                 (create_sharing_decls (List.map #1 srts))
                 (List.map (sort_to_string o #1) srts
                  @ List.map
                      (fn srt => sort_to_string srt ^ "Var")
                      (List.filter (#hasvar ana) (#mutual ana srt))))
    end

fun doit_user sig_name (ana : ana) =
    let
      val symbols =
          interleave BlankDecl
            (List.map
               (fn sym =>
                   StructureDecl
                     (Big (sym_to_string sym),
                      SigVar "TEMP"))
               (#symbs ana))

      val asts =
          interleave BlankDecl
            (List.map
               (fn (ast, (args, _)) => ast_decl ast args)
               (#asts ana))

      val sorts =
          interleave BlankDecl
            (List.concat
               (List.map (create_mutual_sort_structure_decls ana) (#sorts ana)))
    in
      Emit.emit
        [TLSignature
           (sig_name,
            SigBody (symbols @ [BlankDecl] @ asts @ [BlankDecl] @ sorts))]
    end
end
