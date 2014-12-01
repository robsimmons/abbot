(* Abbot: implementating abstract binding trees (___.abt.impl.sml) *)

structure AbbotImpl =
struct

open Util
infixr 0 >>
open Analysis
open AbbotCore
open SmlSyntax

fun with_index f x =
    let val index = ref 0
    in f (fn () => (index := !index + 1; Int.toString (!index))) x
    end

val create_symbol_structures =
    List.map
      (fn sym =>
          StructureDefn
            (Big (sym_to_string sym),
             NONE,
             StructVar "Temp"))

fun internalize_binding binding =
    case binding of
        SortBinding _ => ProdBinding []
      | SymbolBinding _ => ProdBinding []
      | ProdBinding bindings =>
        ProdBinding (List.map internalize_binding bindings)
      | ListBinding binding =>
        ListBinding (internalize_binding binding)
      | AppBinding (ast, bindings) =>
        AppBinding (ast, List.map internalize_binding bindings)

fun internalize_arity arity =
    case arity of
        SortArity srt => SortArity srt
      | SymbolArity sym => SymbolArity sym
      | ProdArity aritys =>
        ProdArity (List.map internalize_arity aritys)
      | ListArity arity =>
        ListArity (internalize_arity arity)
      | AppArity (ast, aritys) =>
        AppArity (ast, List.map internalize_arity aritys)
      | BindingArity (binding, arity) =>
        BindingArity (internalize_binding binding, internalize_arity arity)

fun binding_to_pat' index binding =
    case binding of
        SortBinding srt =>
        VarPat (sort_to_string srt ^ index ())
      | SymbolBinding sym =>
        VarPat (sym_to_string sym ^ index ())
      | ProdBinding bindings =>
        TuplePat (List.map (binding_to_pat' index) bindings)
      | ListBinding binding =>
        VarPat ("list" ^ index ())
      | AppBinding (ast, bindings) =>
        VarPat (ast_to_string ast ^ index ())

val binding_to_pat = with_index binding_to_pat'

fun arity_to_pat' index arity =
    case arity of
        SortArity srt =>
        VarPat (sort_to_string srt ^ index ())
      | SymbolArity sym =>
        VarPat (sym_to_string sym ^ index ())
      | ProdArity aritys =>
        TuplePat (List.map (arity_to_pat' index) aritys)
      | ListArity arity =>
        VarPat ("list" ^ index ())
      | AppArity (ast, arity) =>
        VarPat (ast_to_string ast ^ index ())
      | BindingArity (binding, arity) =>
        TuplePat [binding_to_pat' index binding, arity_to_pat' index arity]

val arity_to_pat = with_index arity_to_pat'

fun unbind_single ana srt exp =
    SeqExp
      [ExpVar "List.foldr",
       LamExp
         [(TuplePat [VarPat "x", VarPat "acc"],
           LetExp
             ([ValDefn
                 (InjPat ("Abt.Binding", TuplePat [VarPat "y", VarPat "acc'"]),
                  SeqExp
                    [ExpVar "Abt.out",
                     ExpVar
                       (ops_name ana srt ^ "."
                        ^ sort_to_string srt ^ "_oper_unbind"),
                     SeqExp
                       [ExpVar "Abt.unbind",
                        ExpVar
                          (ops_name ana srt ^ "."
                          ^ sort_to_string srt ^ "_oper_unbind"),
                        ExpVar "x",
                        ExpVar "~1", (* This violates every invariant... *)
                        ExpVar "acc"]])],
              ExpVar "acc'"))],
       exp,
       ExpVar "vars"]

fun place_vars' index binding =
    case binding of
        SortBinding srt =>
        (index ();
         LetExp
           ([ValDefn
               (VarPat "x", SeqExp [ExpVar "Temp.new", StringExp "x"])],
            TupleExp [ExpVar "x", ListExp [ExpVar "x"]]))
      | SymbolBinding sym =>
        (index ();
         LetExp
           ([ValDefn
               (VarPat "x", SeqExp [ExpVar "Temp.new", StringExp "x"])],
            TupleExp [ExpVar "x", ListExp [ExpVar "x"]]))
      | ProdBinding bindings =>
        LetExp
          (mapi
             (fn (i, binding) =>
                 ValDefn
                   (VarPat ("x" ^ Int.toString i ^ "'"),
                    place_vars' index binding))
             bindings,
           TupleExp
             [TupleExp
                (mapi
                   (fn (i, _) =>
                       SeqExp [ExpVar "#1", ExpVar ("x" ^ Int.toString i ^ "'")])
                   bindings),
              SeqExp
                [ExpVar "List.concat",
                 ListExp
                   (mapi
                      (fn (i, _) =>
                          SeqExp [ExpVar "#2", ExpVar ("x" ^ Int.toString i ^ "'")])
                      bindings)]])
      | ListBinding binding =>
        SeqExp
          [ExpVar "List.iter",
           LamExp
             [(TuplePat [binding_to_pat binding, VarPat "acc"],
              LetExp
                ([ValDefn
                    (TuplePat [TuplePat [VarPat "binding", VarPat "vars"]],
                     place_vars binding)],
                 TupleExp
                   [ExpVar "binding",
                    SeqExp [ExpVar "vars", ExpVar "@", ExpVar "acc"]]))],
           TupleExp [ExpVar ("list" ^ index ()), ListExp []]]
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] => TupleExp [ExpVar (ast_to_string ast ^ index ()), ListExp []]
           | _ =>
             SeqExp
               (ExpVar (Big (ast_to_string ast) ^ ".iter")
                :: List.map
                     (fn binding =>
                         LamExp
                           [(TuplePat [binding_to_pat binding, VarPat "acc"],
                             LetExp
                               ([ValDefn
                                   (TuplePat
                                      [VarPat "binding", VarPat "vars"],
                                    place_vars binding)],
                                TupleExp
                                  [ExpVar "binding",
                                   SeqExp
                                     [ExpVar "vars",
                                      ExpVar "@",
                                      ExpVar "acc"]]))])
                        bindings
                @ [TupleExp
                     [ExpVar (ast_to_string ast ^ index ()),
                      ListExp []]]))

and place_vars binding =
    with_index place_vars' binding

fun arity_to_exp_out' ana index arity =
    case arity of
        SortArity srt =>
        unbind_single ana srt (ExpVar (sort_to_string srt ^ index ()))
      | SymbolArity sym =>
        ExpVar (sym_to_string sym ^ index ())
      | ProdArity aritys =>
        TupleExp (List.map (arity_to_exp_out' ana index) aritys)
      | ListArity arity =>
        SeqExp
          [ExpVar "List.map",
           LamExp [(arity_to_pat arity, arity_to_exp_out ana arity)],
           ExpVar ("list" ^ index ())]
      | AppArity (ast, aritys) =>
        (case aritys of
             [] => ExpVar (ast_to_string ast ^ index ())
           | _ =>
             SeqExp
               [ExpVar "#1",
                SeqExp
                  (ExpVar (Big (ast_to_string ast) ^ ".iter")
                   :: List.map
                        (fn arity =>
                            LamExp
                              [(TuplePat
                                  [arity_to_pat arity,
                                   TuplePat []],
                                TupleExp
                                  [arity_to_exp_out ana arity,
                                   TupleExp []])])
                        aritys
                   @ [TupleExp
                        [ExpVar (ast_to_string ast ^ index ()),
                         TupleExp []]])])
      | BindingArity (binding, arity) =>
        LetExp
          ([ValDefn
              (TuplePat [VarPat "binding", VarPat "vars'"],
               place_vars' index binding),
            ValDefn
              (VarPat "vars",
               SeqExp [ExpVar "vars", ExpVar "@", ExpVar "vars'"])],
           TupleExp
             [ExpVar "binding",
              arity_to_exp_out' ana index arity])

and arity_to_exp_out ana =
    with_index (arity_to_exp_out' ana)

fun map_binding_to_exp' f index binding =
    case binding of
        SortBinding srt =>
        f (srt, ExpVar (sort_to_string srt ^ "Var" ^ index ()))
      | SymbolBinding sym =>
        ExpVar (sym_to_string sym ^ index ())
      | ProdBinding bindings =>
        TupleExp (List.map (map_binding_to_exp' f index) bindings)
      | ListBinding binding =>
        SeqExp
          [ExpVar "List.map",
           LamExp [(binding_to_pat binding, map_binding_to_exp f binding)],
           ExpVar ("list" ^ index ())]
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] => ExpVar (ast_to_string ast ^ index ())
           | _ =>
             SeqExp
               [ExpVar "#1",
                SeqExp
                  (ExpVar (Big (ast_to_string ast) ^ ".iter")
                   :: List.map
                        (fn binding =>
                            LamExp
                              [(TuplePat [binding_to_pat binding, TuplePat []],
                                TupleExp
                                  [map_binding_to_exp f binding,
                                   TupleExp []])])
                        bindings
                   @ [TupleExp
                        [ExpVar (ast_to_string ast ^ index ()),
                         TupleExp []]])])

and map_binding_to_exp f =
    with_index (map_binding_to_exp' f)

fun map_arity_to_exp' f index arity =
    case arity of
        SortArity srt =>
        f (srt, ExpVar (sort_to_string srt ^ index ()))
      | SymbolArity sym =>
        ExpVar (sym_to_string sym ^ index ())
      | ProdArity aritys =>
        TupleExp (List.map (map_arity_to_exp' f index) aritys)
      | ListArity arity =>
        SeqExp
          [ExpVar "List.map",
           LamExp [(arity_to_pat arity, map_arity_to_exp arity f)],
           ExpVar ("list" ^ index ())]
      | AppArity (ast, aritys) =>
        (case aritys of
             [] => ExpVar (ast_to_string ast ^ index ())
           | _ =>
             SeqExp
               [ExpVar "#1",
                SeqExp
                  (ExpVar (Big (ast_to_string ast) ^ ".iter")
                   :: List.map
                        (fn arity =>
                            LamExp
                              [(TuplePat [arity_to_pat arity, TuplePat []],
                                TupleExp
                                  [map_arity_to_exp arity f,
                                   TupleExp []])])
                        aritys
                   @ [TupleExp
                        [ExpVar (ast_to_string ast ^ index ()),
                         TupleExp []]])])
      | BindingArity (binding, arity) =>
        TupleExp
          [map_binding_to_exp' f index binding,
           map_arity_to_exp' f index arity]

and map_arity_to_exp arity f =
    with_index (map_arity_to_exp' f) arity

fun extract_vars' index binding =
    case binding of
        SortBinding srt =>
        TupleExp
          [TupleExp [],
           ListExp [ExpVar (sort_to_string srt ^ index ())]]
      | SymbolBinding sym =>
        TupleExp
          [TupleExp [],
           ListExp [ExpVar (sym_to_string sym ^ index ())]]
      | ProdBinding bindings =>
        LetExp
          (mapi
             (fn (i, binding) =>
                 ValDefn
                   (VarPat ("x" ^ Int.toString i ^ "'"),
                    extract_vars' index binding))
             bindings,
           TupleExp
             [TupleExp
                (mapi
                   (fn (i, _) =>
                       SeqExp [ExpVar "#1", ExpVar ("x" ^ Int.toString i ^ "'")])
                   bindings),
              SeqExp
                [ExpVar "List.concat",
                 ListExp
                   (mapi
                      (fn (i, _) =>
                          SeqExp [ExpVar "#2", ExpVar ("x" ^ Int.toString i ^ "'")])
                      bindings)]])
      | ListBinding binding =>
        SeqExp
          [ExpVar "List.iter",
           LamExp
             [(TuplePat [binding_to_pat binding, VarPat "acc"],
               LetExp
                 ([ValDefn
                     (TuplePat [VarPat "binding", VarPat "vars"],
                      extract_vars binding)],
                  TupleExp
                    [ExpVar "binding",
                     SeqExp [ExpVar "vars", ExpVar "@", ExpVar "acc"]]))],
           TupleExp [ExpVar ("list" ^ index ()), ListExp []]]
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] => TupleExp [ExpVar (ast_to_string ast ^ index ()), ListExp []]
           | _ =>
             SeqExp
               (ExpVar (Big (ast_to_string ast) ^ ".iter")
                :: List.map
                     (fn binding =>
                         LamExp
                           [(TuplePat [binding_to_pat binding, VarPat "acc"],
                             LetExp
                               ([ValDefn
                                   (TuplePat
                                      [VarPat "binding",
                                       VarPat "vars"],
                                    extract_vars binding)],
                                TupleExp
                                  [ExpVar "binding",
                                   SeqExp
                                     [ExpVar "vars",
                                      ExpVar "@",
                                      ExpVar "acc"]]))])
                        bindings
                @ [TupleExp
                     [ExpVar (ast_to_string ast ^ index ()),
                      ListExp []]]))

and extract_vars binding =
    with_index extract_vars' binding

fun bind_single ana srt exp =
    SeqExp
      [ExpVar "List.foldl",
       LamExp
         [(TuplePat [VarPat "x", VarPat "acc"],
           SeqExp
             [ExpVar "Abt.into",
              ExpVar
                (ops_name ana srt ^ "." ^ sort_to_string srt ^ "_oper_bind"),
              SeqExp
                [ExpVar ("Abt.Binding"),
                 TupleExp [ExpVar "x", ExpVar "acc"]]])],
       exp,
       ExpVar "vars"]

fun arity_to_exp_in' (ana : ana) index arity =
    case arity of
        SortArity srt =>
        bind_single ana srt (ExpVar (sort_to_string srt ^ index ()))
      | SymbolArity sym =>
        ExpVar (sym_to_string sym ^ index ())
      | ProdArity aritys =>
        TupleExp (List.map (arity_to_exp_in' ana index) aritys)
      | ListArity arity =>
        SeqExp
          [ExpVar "List.map",
           LamExp [(arity_to_pat arity, arity_to_exp_in ana arity)],
           ExpVar ("list" ^ index ())]
      | AppArity (ast, aritys) =>
        (case aritys of
             [] => ExpVar (ast_to_string ast ^ index ())
           | _ =>
             SeqExp
               [ExpVar "#1",
                SeqExp
                  (ExpVar (Big (ast_to_string ast) ^ ".iter")
                   :: List.map
                        (fn arity =>
                            LamExp
                              [(TuplePat [arity_to_pat arity, TuplePat []],
                                TupleExp
                                  [arity_to_exp_in ana arity,
                                   TupleExp []])])
                        aritys
                   @ [TupleExp
                        [ExpVar (ast_to_string ast ^ index ()),
                         TupleExp []]])])
      | BindingArity (binding, arity) =>
        LetExp
          ([ValDefn
              (TuplePat [VarPat "binding", VarPat "vars'"],
               extract_vars' index binding),
            ValDefn
              (VarPat "vars",
               SeqExp [ExpVar "vars", ExpVar "@", ExpVar "vars'"])],
           TupleExp
             [ExpVar "binding",
              arity_to_exp_in' ana index arity])

and arity_to_exp_in (ana : ana) =
    with_index (arity_to_exp_in' ana)

fun create_mutual_ops (ana : ana) srts =
    let
      fun scoped_sort srt srt' =
          if #mutualwith ana srt srt'
          then sort_to_string srt'
          else ops_name ana srt' ^ "." ^ sort_to_string srt'

      val datatypes =
          List.map
            (fn (srt, opers) =>
                (sort_to_string srt ^ "_oper",
                 [],
                 List.map
                   (fn (oper, arity_opt) =>
                       (sort_to_string srt ^ "'" ^ oper,
                        case arity_opt of
                            NONE => NONE
                          | SOME arity =>
                            SOME
                              (arity_to_type
                                 ana srt true
                                 (internalize_arity arity))))
                   opers))
            srts

      val withtypes =
          List.map
            (fn (srt, _) =>
                (sort_to_string srt,
                 [],
                 App
                   ([TypeVar (sort_to_string srt ^ "_oper")],
                    ModProj ("Abt", TypeVar "t"))))
            srts

      fun oper_rec name args (srt, opers) =
          (sort_to_string srt ^ "_oper_" ^ name,
           List.map VarPat args @ [VarPat (sort_to_string srt)],
           NONE,
           CaseExp
             (ExpVar (sort_to_string srt),
              List.map
                (fn (oper, arity_opt) =>
                    case arity_opt of
                        NONE =>
                        (VarPat (sort_to_string srt ^ "'" ^ oper),
                         ExpVar (sort_to_string srt ^ "'" ^ oper))
                      | SOME arity =>
                        let val arity' = internalize_arity arity in
                          (InjPat
                             (sort_to_string srt ^ "'" ^ oper,
                              arity_to_pat arity'),
                           SeqExp [ExpVar (sort_to_string srt ^ "'" ^ oper),
                                   map_arity_to_exp arity'
                                     (fn (srt', exp) =>
                                         SeqExp
                                           (List.concat
                                              [[ExpVar ("Abt." ^ name),
                                                ExpVar
                                                  (scoped_sort srt srt'
                                                   ^ "_oper_"
                                                   ^ name)],
                                               List.map ExpVar args,
                                               [exp]]))])
                        end)
                opers))

      fun aequiv_code (srt, opers) =
          (sort_to_string srt ^ "_oper_aequiv",
           [TuplePat [VarPat "l", VarPat "r"]],
           NONE,
           SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])

      fun toString_code (srt, opers) =
          (sort_to_string srt ^ "_oper_toString",
           [VarPat (sort_to_string srt)],
           NONE,
           SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])
    in
      StructureDefn
        (String.concat (List.map (Big o sort_to_string o #1) srts) ^ "Ops",
         NONE,
         StructBody
           ([TypeDefns {datatypes = datatypes, aliases = withtypes},
             FunDefn (List.map (oper_rec "bind" ["x", "i"]) srts),
             FunDefn (List.map (oper_rec "unbind" ["x", "i"]) srts),
             FunDefn (List.map aequiv_code srts),
             FunDefn (List.map toString_code srts)]))
    end

(* Code duplication??? *)
fun create_view_datatype_defn ana (srt, opers) =
    let
      val args = List.map (fn srt => "'" ^ sort_to_string srt) (#mutual ana srt)

      val oper_branches =
          List.map
            (fn (oper, arity_opt) =>
                (oper,
                 case arity_opt of
                     NONE => NONE
                   | SOME arity => SOME (arity_to_type ana srt false arity)))
            opers

      val body =
          if #hasvar ana srt
          then ("Var", SOME (sort_to_var_type srt)) :: oper_branches
          else oper_branches
    in
      TypeDefns {datatypes = [("view", args, body)], aliases = []}
    end

fun oper_to_case_in ana srt (oper, arity_opt) =
    case arity_opt of
        NONE =>
        (VarPat oper,
         SeqExp
           [ExpVar "Abt.Oper",
            ExpVar (ops_name ana srt ^ "." ^ sort_to_string srt ^ "'" ^ oper)])
      | SOME arity =>
        (InjPat (oper, arity_to_pat arity),
         LetExp
           ([ValDefn (VarPat "vars", ListExp [])],
            SeqExp
              [ExpVar "Abt.Oper",
               SeqExp
                 [ExpVar
                    (ops_name ana srt ^ "." ^ sort_to_string srt ^ "'" ^ oper),
                  arity_to_exp_in ana arity]]))

fun oper_to_case_out ana srt (oper, arity_opt) =
    case arity_opt of
        NONE =>
        (InjPat
           ("Abt.Oper",
            VarPat (ops_name ana srt ^ "." ^ sort_to_string srt ^ "'" ^ oper)),
         ExpVar oper)
      | SOME arity =>
        (InjPat
           ("Abt.Oper",
            InjPat
              (ops_name ana srt ^ "." ^ sort_to_string srt ^ "'" ^ oper,
               arity_to_pat arity)),
         LetExp
           ([ValDefn (VarPat "vars", ListExp [])],
            SeqExp [ExpVar oper, arity_to_exp_out ana arity]))

fun create_sort_structure_defn (ana : ana) (srt, opers) =
    let
      val mutual_type_defns =
          let val srts = #mutual ana srt in
            List.map
              (fn srt =>
                  TypeDefns
                    {datatypes = [],
                     aliases =
                     [(sort_to_string srt,
                       [],
                       ModProj
                         (String.concat
                            (List.map (Big o sort_to_string) srts)
                          ^ "Ops",
                          sort_to_type true srt))]})
              srts
          end

      val mutual_var_defns =
          List.map
            (fn var_srt =>
                TypeDefns
                  {datatypes = [],
                   aliases =
                   [(sort_to_string var_srt ^ "Var",
                     [],
                     ModProj ("Temp", TypeVar "t"))]})
            (List.filter (#hasvar ana) (#mutual ana srt))

      val var_structure_defn =
          if #hasvar ana srt
          then [StructureDefn ("Var", NONE, StructVar "Temp")]
          else []

      val convenient_contructors =
          let
            val oper_constructors =
                List.map
                  (fn (oper, arity_opt) =>
                      ValDefn
                        (VarPat (oper ^ "'"),
                         (case arity_opt of
                              NONE => SeqExp [ExpVar "into", ExpVar oper]
                            | SOME _ =>
                              SeqExp
                                [ExpVar "into", ExpVar "o", ExpVar oper])))
                  opers
          in
            if #hasvar ana srt
            then
              ValDefn
                (VarPat "Var'",
                 SeqExp [ExpVar "into", ExpVar "o", ExpVar "Var"])
              :: oper_constructors
            else oper_constructors
          end

      val view_in_code =
          FunDefn
            [("view_in",
              [VarPat "v"],
              NONE,
              CaseExp
                (ExpVar "v",
                 let val cases = List.map (oper_to_case_in ana srt) opers in
                   if #hasvar ana srt
                   then
                     (InjPat ("Var", VarPat (sort_to_string srt ^ "Var")),
                      SeqExp
                        [ExpVar "Abt.Var",
                         ExpVar (sort_to_string srt ^ "Var")])
                     :: cases
                   else cases
                 end))]

      val view_out_code =
          FunDefn
            [("view_out",
              [VarPat "v"],
              NONE,
              CaseExp
                (ExpVar "v",
                 let
                   val cases =
                       List.map (oper_to_case_out ana srt) opers
                       @ [(Wild,
                           SeqExp
                             [ExpVar "raise",
                              ExpVar "Fail",
                              StringExp "Internal Abbot Error"])]
                 in
                   if #hasvar ana srt
                   then
                     (InjPat
                        ("Abt.Var",
                         VarPat (sort_to_string srt ^ "Var")),
                      SeqExp
                        [ExpVar "Var",
                         ExpVar (sort_to_string srt ^ "Var")])
                     :: cases
                   else cases
                 end))]

      val into_code =
          FunDefn
            [("into",
              [VarPat "v"],
              NONE,
              SeqExp
                [ExpVar "Abt.into",
                 ExpVar
                   (ops_name ana srt
                    ^ "." ^ sort_to_string srt ^ "_oper_bind"),
                 SeqExp [ExpVar "view_in", ExpVar "v"]])]

      val out_code =
          FunDefn
            [("out",
              [VarPat (sort_to_string srt)],
              NONE,
              SeqExp
                [ExpVar "view_out",
                 SeqExp
                   [ExpVar "Abt.out",
                    ExpVar
                      (ops_name ana srt
                       ^ "." ^ sort_to_string srt ^ "_oper_unbind"),
                    ExpVar (sort_to_string srt)]])]

      val aequiv_code =
          FunDefn
            [("aequiv",
              [TuplePat [VarPat "l", VarPat "r"]],
              NONE,
              SeqExp
                [ExpVar "Abt.aequiv",
                 ExpVar
                   (ops_name ana srt
                    ^ "." ^ sort_to_string srt ^ "_oper_aequiv"),
                 TupleExp [ExpVar "l", ExpVar "r"]])]

      val toString_code =
          FunDefn
            [("toString",
              [VarPat (sort_to_string srt)],
              NONE,
              SeqExp
                [ExpVar "Abt.toString",
                 ExpVar
                   (ops_name ana srt
                    ^ "." ^ sort_to_string srt ^ "_oper_toString"),
                 ExpVar (sort_to_string srt)])]

      val map_code =
          FunDefn
            [("map",
              [VarPat "f"],
              NONE,
              SeqExp
                [ExpVar "view_out",
                 ExpVar "o",
                 ExpVar "Abt.map",
                 ExpVar "f",
                 ExpVar "o",
                 ExpVar "view_in"])]

      val substitutions =
          List.map
            (fn srt' =>
                FunDefn
                  [(if srt = srt'
                    then "subst"
                    else "subst" ^ Big (sort_to_string srt'),
                    [VarPat (sort_to_string srt' ^ "1"),
                     VarPat "x",
                     VarPat (sort_to_string srt ^ "2")],
                    NONE,
                    SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])])
            (List.filter (#hasvar ana) (#dependencies ana srt))

      val all_defns =
          List.concat
            [mutual_type_defns,
             [TypeDefns
                {datatypes = [],
                 aliases = [("t", [], TypeVar (sort_to_string srt))]}],
             mutual_var_defns,
             [BlankDefn],
             var_structure_defn,
             [BlankDefn,
              create_view_datatype_defn ana (srt, opers),
              BlankDefn,
              view_in_code,
              BlankDefn,
              view_out_code,
              BlankDefn,
              into_code,
              out_code,
              aequiv_code,
              toString_code,
              map_code],
             (case substitutions of
                  [] => []
                | _ => BlankDefn :: substitutions),
             [BlankDefn],
             convenient_contructors]
    in
      StructureDefn (Big (sort_to_string srt), NONE, StructBody all_defns)
    end

fun ast_datatype ana ast args opers =
    ("t",
     List.map (fn arg => "'" ^ arg) args,
     List.map
       (fn (oper, arity_opt) =>
           (oper,
            case arity_opt of
                NONE => NONE
              | SOME arity => SOME (ast_arity_to_type ana ast arity)))
       opers)

fun ast_arity_to_pat' index arity =
    case arity of
        Param str => VarPat (str ^ index ())
      | ProdAstArity aritys =>
        TuplePat (List.map (ast_arity_to_pat' index) aritys)
      | AppAstArity (ast, aritys) =>
        VarPat (ast_to_string ast ^ index ())
      | ListAstArity arity =>
        VarPat ("list" ^ index ())

val ast_arity_to_pat = with_index ast_arity_to_pat'

fun ast_arity_to_exp' ast index arity =
    case arity of
        Param str =>
        SeqExp
          [ExpVar ("f" ^ str),
           TupleExp [ExpVar (str ^ index ()), ExpVar "state"]]
      | ProdAstArity aritys =>
        LetExp
          (mapi
             (fn (i, arity) =>
                 ValDefn
                   (TuplePat [VarPat ("x" ^ Int.toString i), VarPat "state"],
                    ast_arity_to_exp' ast index arity))
             aritys,
           TupleExp
             [TupleExp
                (mapi
                   (fn (i, _) => ExpVar ("x" ^ Int.toString i))
                   aritys),
              ExpVar "state"])
      | AppAstArity (ast', aritys) =>
        (case aritys of
            [] =>
            TupleExp
              [ExpVar (ast_to_string ast' ^ index ()),
               ExpVar "state"]
          | _ =>
            SeqExp
              ((if ast = ast'
                then ExpVar "iter"
                else ExpVar (Big (ast_to_string ast' ^ ".iter")))
               :: List.map
                    (fn arity =>
                        LamExp
                          [(TuplePat [ast_arity_to_pat arity, VarPat "state"],
                            ast_arity_to_exp ast arity)])
                    aritys
               @ [TupleExp
                    [ExpVar (ast_to_string ast' ^ index ()),
                     ExpVar "state"]]))
      | ListAstArity arity =>
        SeqExp
          [ExpVar "List.iter",
           LamExp
             [(TuplePat [ast_arity_to_pat arity, VarPat "state"],
               ast_arity_to_exp ast arity)],
           TupleExp [ExpVar ("list" ^ index ()), ExpVar "state"]]

and ast_arity_to_exp ast = with_index (ast_arity_to_exp' ast)

fun ast_iter ana ast args opers =
    FunDefn
      [("iter",
        (List.map (fn arg => VarPat ("f" ^ arg)) args)
        @ [TuplePat [VarPat "t", VarPat "state"]],
        NONE,
        CaseExp
          (ExpVar "t",
           List.map
             (fn (oper, arity_opt) =>
                 case arity_opt of
                     NONE =>
                     (VarPat oper, TupleExp [ExpVar oper, ExpVar "state"])
                   | SOME arity =>
                     (InjPat (oper, ast_arity_to_pat arity),
                      LetExp
                        ([(ValDefn
                             (TuplePat [VarPat "t", VarPat "state"],
                              ast_arity_to_exp ast arity))],
                         TupleExp
                           [SeqExp [ExpVar oper, ExpVar "t"],
                            ExpVar "state"])))
             opers))]

fun doit_impl sig_name struct_name (ana : ana) =
    let
      val external_ast_decls =
          mapfilter
            (fn (ast, (args, opers)) =>
                case opers of
                    [] => SOME (ast_decl ast args)
                  | _ => NONE)
            (#asts ana)

      val external_ast_defns =
          mapfilter
            (fn (ast, (args, opers)) =>
                case opers of
                    [] =>
                    SOME
                      (StructureDefn
                         (Big (ast_to_string ast),
                          NONE,
                          StructVar (Big (ast_to_string ast))))
                  | _ => NONE)
            (#asts ana)

      val internal_asts =
          mapfilter
            (fn (ast, (args, opers)) =>
                case opers of
                    [] => NONE
                  | _ =>
                    SOME
                      (StructureDefn
                         (Big (ast_to_string ast),
                          NONE,
                          StructBody
                            (case args of
                                 [] =>
                                 [TypeDefns
                                    {datatypes=
                                     [ast_datatype ana ast args opers],
                                     aliases=[]}]
                               | _ =>
                                 [TypeDefns
                                    {datatypes=
                                     [ast_datatype ana ast args opers],
                                     aliases=[]},
                                  ast_iter ana ast args opers]))))
            (#asts ana)

      val list_ast =
          if #haslist ana
          then
            [StructureDefn
               ("List",
                NONE,
                StructBody
                  [OpenDefn (StructVar "List"),
                   FunDefn
                     [("iter",
                       [VarPat "f", TuplePat [VarPat "l", VarPat "state"]],
                       NONE,
                       SeqExp
                         [ExpVar "List.foldr",
                          LamExp
                            [(TuplePat
                                [VarPat "x",
                                 TuplePat [VarPat "l", VarPat "state"]],
                              LetExp
                                ([ValDefn
                                    (TuplePat [VarPat "x'", VarPat "state'"],
                                     SeqExp
                                       [ExpVar "f",
                                        TupleExp [ExpVar "x", ExpVar "state"]])],
                                 TupleExp
                                   [SeqExp
                                      [ExpVar "x'", ExpVar "::", ExpVar "l"],
                                    ExpVar "state'"]))],
                          TupleExp [ListExp [], ExpVar "state"],
                          ExpVar "l"])]])]
          else []

      val symbols = create_symbol_structures (#symbs ana)

      val sorts = List.concat
                     (List.map
                        (fn mutual =>
                            create_mutual_ops ana mutual
                            :: List.map (create_sort_structure_defn ana) mutual)
                        (#sorts ana))

      val defns =
          interleave BlankDefn
            (symbols @ list_ast @ external_ast_defns @ internal_asts @ sorts)
    in
      case external_ast_decls of
          [] =>
          Emit.emit
            [TLStructure
               (struct_name,
                SOME (SigVar sig_name),
                StructBody defns)]
        | _ =>
          Emit.emit
            [TLFunctor
               (struct_name,
                external_ast_decls,
                SOME (SigVar sig_name),
                StructBody defns)]
    end
end
