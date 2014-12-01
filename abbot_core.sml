(* Core functionality about the way abbot maps sorts to SML types *)

structure AbbotCore =
struct

open Util
infixr 0 >>
open Analysis
open SMLSyntax

fun Big s =
    Char.toString (Char.toUpper (String.sub (s, 0)))
    ^ String.extract (s, 1, NONE)

fun BIG s = String.map Char.toUpper s

fun sort_to_type concrete s =
    TypeVar (if concrete then sort_to_string s else "'" ^ sort_to_string s)

fun sort_to_var_type s =
    TypeVar (sort_to_string s ^ "Var")

fun sym_to_type s =
    TypeVar (sym_to_string s)

fun polymorphic_view (ana : ana) srt post =
    App
      (List.map
         (fn srt => TypeVar ("'" ^ sort_to_string srt ^ post))
         (#mutual ana srt),
       TypeVar "view")

fun concrete_view (ana : ana) srt =
    App (List.map (sort_to_type true) (#mutual ana srt), TypeVar "view")

fun binding_to_type (ana : ana) srt concrete binding =
    case binding of
        SortBinding srt' =>
        if #mutualwith ana srt srt'
        then sort_to_var_type srt'
        else ModProj (Big (sort_to_string srt'), sort_to_var_type srt')
      | SymbolBinding sym => ModProj (Big (sym_to_string sym), TypeVar "t")
      | ProdBinding bindings =>
        Prod (List.map (binding_to_type ana srt concrete) bindings)
      | ListBinding binding =>
        App ([binding_to_type ana srt concrete binding], TypeVar "list")
      | AppBinding (ast, bindings) =>
        App
          (List.map (binding_to_type ana srt concrete) bindings,
           ModProj (Big (ast_to_string ast), TypeVar "t"))

fun arity_to_type (ana : ana) srt concrete arity =
    case arity of
        SortArity srt' =>
        if #mutualwith ana srt srt'
        then sort_to_type concrete srt'
        else ModProj (Big (sort_to_string srt'), TypeVar "t")
      | SymbolArity sym => ModProj (Big (sym_to_string sym), TypeVar "t")
      | ProdArity aritys =>
        Prod (List.map (arity_to_type ana srt concrete) aritys)
      | ListArity arity =>
        App ([arity_to_type ana srt concrete arity], TypeVar "list")
      | AppArity (ast, aritys) =>
        App
          (List.map (arity_to_type ana srt concrete) aritys,
           ModProj (Big (ast_to_string ast), TypeVar "t"))
      | BindingArity (binding, arity) =>
        Prod
          [binding_to_type ana srt concrete binding,
           arity_to_type ana srt concrete arity]

fun ast_arity_to_type (ana : ana) ast arity =
    case arity of
        Param str => TypeVar ("'" ^ str)
      | ProdAstArity aritys =>
        Prod (List.map (ast_arity_to_type ana ast) aritys)
      | AppAstArity (ast', aritys) =>
        App
          (List.map (ast_arity_to_type ana ast) aritys,
           if ast = ast'
           then TypeVar ("t")
           else ModProj (Big (ast_to_string ast'), TypeVar "t"))
      | ListAstArity arity =>
        App ([ast_arity_to_type ana ast arity], TypeVar "list")

fun ops_name (ana : ana) srt =
    String.concat (List.map (Big o sort_to_string) (#mutual ana srt)) ^ "Ops"

fun map_binding f g h binding =
    case binding of
        SortBinding srt => SortBinding (h srt)
      | SymbolBinding sym => SymbolBinding (f sym)
      | ProdBinding bindings =>
        ProdBinding (List.map (map_binding f g h) bindings)
      | ListBinding binding =>
        ListBinding (map_binding f g h binding)
      | AppBinding (ast, bindings) =>
        AppBinding (g ast, List.map (map_binding f g h) bindings)

fun map_arity f g h arity =
    case arity of
        SortArity srt => SortArity (h srt)
      | SymbolArity sym => SymbolArity (f sym)
      | ProdArity aritys =>
        ProdArity (List.map (map_arity f g h) aritys)
      | ListArity arity =>
        ListArity (map_arity f g h arity)
      | AppArity (ast, aritys) =>
        AppArity (g ast, List.map (map_arity f g h) aritys)
      | BindingArity (binding, arity) =>
        BindingArity (map_binding f g h binding, map_arity f g h arity)

fun create_ast_signature args =
    SigBody
      ((TypeDecls
          {datatypes=[],
           aliases=
           [("t",
             List.map (fn arg => "'" ^ arg) args, NONE)]})
       :: (case args of
               [] => []
             | _ =>
               [BlankDecl,
                ValDecl
                  ("iter",
                   List.foldr
                     (fn (arg, acc) =>
                         Arrow
                           (Arrow
                              (Prod [TypeVar ("'" ^ arg ^ "1"),
                                     TypeVar "'state"],
                               Prod [TypeVar ("'" ^ arg ^ "2"),
                                     TypeVar "'state"]),
                            acc))
                     (Arrow
                        (Prod
                           [App
                              (List.map
                                 (fn arg => TypeVar ("'" ^ arg ^ "1"))
                                 args,
                               TypeVar "t"),
                            TypeVar "'state"],
                         Prod
                           [App
                              (List.map
                                 (fn arg => TypeVar ("'" ^ arg ^ "2"))
                                 args,
                               TypeVar "t"),
                            TypeVar "'state"]))
                     args)]))

fun ast_decl ast args =
    StructureDecl
      (Big (ast_to_string ast),
       create_ast_signature args)
end
