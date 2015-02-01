(* Abbot: emitting user interface (___.abt.sig) *)

structure AbbotUser =
struct

open Analysis
open SmlSyntax
open AbbotCore

fun create_mutual_type_decls ana abt_or_sort =
    List.map
      (fn {aliases, datatypes} =>
          TypeDecls
            {datatypes = datatypes,
             aliases =
             List.map
               (fn (name, args, _) =>
                   (name, args, NONE))
               aliases})
      (op@ (create_mutual_types ana abt_or_sort))

 fun create_abt_structure_decl ana (abt, (args, opers)) =
    StructureDecl
      (Big (abt_to_string abt),
       SigBody
         (concatWith [BlankDecl]
            [create_mutual_type_decls ana (Abt abt),
             [TypeDecls
                {datatypes=[abt_datatype ana (abt, (args, opers))],
                 aliases=[]}],
             [TypeDecls
                {aliases=[("t", args, SOME (TypeVar (abt_to_string abt)))],
                 datatypes=[]}],
             [ValDecl
                ("aequiv",
                 List.foldr
                   (fn (arg, acc) => ArrowType (TypeVar (arg ^ "_aequiv"), acc))
                   (ArrowType
                      (ProdType
                         [AppType
                            (List.map (fn arg => TypeVar ("'" ^ arg)) args,
                             TypeVar "t"),
                          AppType
                            (List.map (fn arg => TypeVar ("'" ^ arg)) args,
                             TypeVar "t")],
                       TypeVar "bool"))
                   args)]]))

fun create_view_datatype_decl ana (srt, opers) =
    let
      val oper_branches =
          List.map
            (fn (oper, arity_opt) =>
                (oper,
                 (case arity_opt of
                      NONE => NONE
                    | SOME arity =>
                      SOME (sort_arity_to_type ana false srt arity))))
            opers

      val body =
          if #hasvar ana srt
          then ("Var", SOME (TypeVar (sort_to_var_type srt))) :: oper_branches
          else oper_branches
    in
      TypeDecls {datatypes = [("view", [], body)], aliases = []}
    end

fun create_sort_structure_decl (ana : ana) (sort, opers) =
    let
      val var_structure_decl =
          if #hasvar ana sort
          then
            [StructureDecl
               ("Var",
                WhereType
                  (SigVar "TEMP",
                   TypeVar "t",
                   TypeVar (sort_to_var_type sort)))]
          else []

      val convenient_contructors =
          let
            val oper_constructors =
                List.map
                  (fn (oper, arity_opt) =>
                      ValDecl
                        (oper ^ "'",
                         case arity_opt of
                             NONE => sort_to_type sort
                           | SOME arity =>
                             ArrowType
                               (sort_arity_to_type ana false sort arity,
                                sort_to_type sort)))
                  opers
          in
            if #hasvar ana sort
            then
              ValDecl
                ("Var'",
                 ArrowType
                   (TypeVar (sort_to_var_type sort),
                    sort_to_type sort))
              :: oper_constructors
            else
              oper_constructors
          end

      val substitutions =
          List.map
            (fn sort' =>
                ValDecl
                  (if sort = sort'
                   then "subst"
                   else "subst" ^ Big (sort_to_string sort'),
                   ArrowType
                     ((if #mutualwith ana (Sort sort) (Sort sort')
                       then sort_to_type sort'
                       else TypeVar (Big (sort_to_string sort') ^ ".t")),
                      ArrowType
                        ((if #mutualwith ana (Sort sort) (Sort sort')
                          then TypeVar (sort_to_var_type sort')
                          else TypeVar (Big (sort_to_string sort') ^ ".Var.t")),
                         ArrowType (sort_to_type sort, sort_to_type sort)))))
            (List.filter (#hasvar ana) (#2 (#dependencies ana (Sort sort))))

      val all_decls =
          List.concat
            [create_mutual_type_decls ana (Sort sort),
             [TypeDecls
                {datatypes = [],
                 aliases = [(sort_to_string sort, [], NONE)]},
              TypeDecls
                {datatypes = [],
                 aliases = [("t", [], SOME (sort_to_type sort))]},
              BlankDecl],
             var_structure_decl,
             [BlankDecl,
              create_view_datatype_decl ana (sort, opers),
              BlankDecl],
             convenient_contructors,
             [BlankDecl,
              ValDecl
                ("into", ArrowType (TypeVar "view", sort_to_type sort)),
              ValDecl
                ("out", ArrowType (sort_to_type sort, TypeVar "view")),
              ValDecl
                ("aequiv",
                 ArrowType
                   (ProdType [sort_to_type sort, sort_to_type sort],
                    TypeVar "bool")),
              ValDecl
                ("toString", ArrowType (sort_to_type sort, TypeVar "string"))],
             (case substitutions of [] => [] | _ => BlankDecl :: substitutions)]
    in
      StructureDecl (Big (sort_to_string sort), SigBody all_decls)
    end

fun create_sharing_decls mods field =
    case mods of
        [x] => []
      | x::y::mods' =>
        SharingDecl
          (ModProjType (StructVar (Big x), field),
           ModProjType (StructVar (Big y), field))
        :: create_sharing_decls (y::mods') field

fun create_mutual_abt_and_sort_structure_decls ana abts_and_sorts =
    let
      val abt_and_sort_structures =
          List.map
            (fn Sum2.In1 abt => create_abt_structure_decl ana abt
            | Sum2.In2 sort => create_sort_structure_decl ana sort)
            abts_and_sorts

      val abt_and_sort_strings =
          List.map
            (fn Sum2.In1 (abt, _) => abt_to_string abt
            | Sum2.In2 (sort, _) => sort_to_string sort)
            abts_and_sorts

      fun remove_data abt_or_sort =
          case abt_or_sort of
              Sum2.In1 (abt, _) => Abt abt
            | Sum2.In2 (sort, _) => Sort sort
    in
      case abts_and_sorts of
          ([] | [_]) => abt_and_sort_structures
        | abt_or_sort :: _ =>
          abt_and_sort_structures
          @ List.concat
              (List.map
                 (create_sharing_decls abt_and_sort_strings)
                 (abt_and_sort_strings
                  @ List.map
                      (fn sort => sort_to_string sort ^ "Var")
                      (List.filter (#hasvar ana) (#2 (#mutual ana (remove_data abt_or_sort))))))
    end

fun doit_user sig_name (ana : ana) =
    let
      val symbols =
          List.map
            (fn sym =>
                StructureDecl
                  (Big (sym_to_string sym),
                   SigVar "TEMP"))
            (#symbols ana)

      val exts =
          List.map
            (fn (ext, args) =>
                StructureDecl
                  (Big (ext_to_string ext),
                   create_ext_signature args))
            (#externals ana)

      val abts_and_sorts =
          List.concat
            (List.map
               (create_mutual_abt_and_sort_structure_decls ana)
               (#abts_and_sorts ana))
    in
      Emit.emit
        [TLSignature
           (sig_name,
            SigBody
              (symbols
               @ [BlankDecl]
               @ interleave BlankDecl (exts @ abts_and_sorts)))]
    end
end
