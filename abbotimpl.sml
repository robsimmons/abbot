(* Abbot: implementating abstract binding trees (___.abt.impl.sml) *)

structure AbbotImpl =
struct

open Util
infixr 0 >>
open Analysis
open AbbotCore
open AbstractSML

val create_symbol_structures =
    List.map
      (fn sym =>
          StructureDefn
            (Big (sym_to_string sym),
             NONE,
             StructVar "Variable"))

fun internalize_binding binding =
    case binding of
        SortBinding _ => ProdBinding []
      | SymbolBinding _ => ProdBinding []
      | ProdBinding bindings =>
        ProdBinding (List.map internalize_binding bindings)
      | AppBinding (ast, bindings) =>
        AppBinding (ast, List.map internalize_binding bindings)

fun internalize_arity arity =
    case arity of
        SortArity srt => SortArity srt
      | SymbolArity sym => SymbolArity sym
      | ProdArity aritys =>
        ProdArity (List.map internalize_arity aritys)
      | AppArity (ast, aritys) =>
        AppArity (ast, List.map internalize_arity aritys)
      | BindingArity (binding, arity) =>
        BindingArity (internalize_binding binding, internalize_arity arity)

fun binding_to_pat' index binding =
    case binding of
        SortBinding srt =>
        VarPat (sort_to_string srt ^ Int.toString (index ()))
      | SymbolBinding sym =>
        VarPat (sym_to_string sym ^ Int.toString (index ()))
      | ProdBinding bindings =>
        TuplePat (List.map (binding_to_pat' index) bindings)
      | AppBinding (ast, bindings) =>
        VarPat (ast_to_string ast ^ Int.toString (index ()))

fun binding_to_pat binding =
    let val index = ref 0
    in binding_to_pat' (fn () => (index := !index + 1; !index)) binding
    end

fun arity_to_pat' index arity =
    case arity of
        SortArity srt =>
        VarPat (sort_to_string srt ^ Int.toString (index ()))
      | SymbolArity sym =>
        VarPat (sym_to_string sym ^ Int.toString (index ()))
      | ProdArity aritys =>
        TuplePat (List.map (arity_to_pat' index) aritys)
      | AppArity (ast, arity) =>
        VarPat (ast_to_string ast ^ Int.toString (index ()))
      | BindingArity (binding, arity) =>
        TuplePat [binding_to_pat' index binding, arity_to_pat' index arity]

fun arity_to_pat arity =
    let val index = ref 0
    in arity_to_pat' (fn () => (index := !index + 1; !index)) arity
    end

(*
fun unbind_single ana srt exp =
    LetExp
      ([ValDefn
          (InjPat ("Abt.Binding",
                   TuplePat [VarPat "x", VarPat "t"]),
           SeqExp
             [ExpVar "Abt.out",
              ExpVar
                (ops_name ana srt ^ "."
                 ^ sort_to_string srt ^ "_oper_unbind"),
              exp])],
       TupleExp [ExpVar "x", ExpVar "t"])

fun unbind_binding ana srt binding_exp exp binding =
    case binding of
        SortBinding _ => unbind_single ana srt exp
      | SymbolBinding _ => unbind_single ana srt exp
      (*| ProdBinding bindings =>*)
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] => TupleExp [binding_exp, exp]
           | _ =>
             SeqExp
               (ExpVar (Big (ast_to_string ast))
                :: List.map
                     (fn binding =>
                         LamExp
                           [(TuplePat [VarPat "binding", VarPat "t"],
                             binding_to_exp_external ana srt
                               (ExpVar "binding") (ExpVar "t")
                               binding)])
                     bindings
                @ [TupleExp [binding_exp, exp]]))

fun unbind_vars ana srt exp bindings =
    List.foldl
      (fn (binding, exp) =>
          LetExp
            ([ValDefn (TuplePat [VarPat "binding", VarPat "t"], exp)],
             unbind_binding ana srt (ExpVar "binding") (ExpVar "t") binding))
      exp bindings

fun arity_to_exp_external ana srt vars arity =
    case arity of
        SortArity srt' =>
        if srt = srt'
        then
          LetExp
            ([ValDefn (ConsPat (VarPat "hd", VarPat "tl"), ExpVar "self")],
             TupleExp [ExpVar "hd", ExpVar "tl"])
        else
          TupleExp [ExpVar "others", ExpVar "self"]
      | SymbolArity sym =>
        TupleExp [ExpVar "others", ExpVar "self"]
      | ProdArity aritys =>
        LetExp
          (mapi
             (fn (i, arity) =>
                 ValDefn
                   (TuplePat
                      [VarPat ("others" ^ Int.toString i),
                       VarPat "self"],
                    LetExp
                      ([ValDefn
                          (VarPat "others",
                           SeqExp
                             [ExpVar ("#" ^ Int.toString (i + 1)),
                              ExpVar "others"])],
                       arity_to_exp_external ana srt index arity)))
             aritys,
          TupleExp
            [TupleExp
               (mapi
                  (fn (i, _) => ExpVar ("others" ^ Int.toString i))
                  aritys),
             ExpVar "self"])
      | AppArity (ast, aritys) =>
        (case aritys of
             [] => TupleExp [ExpVar "others", ExpVar "self"]
           | _ =>
             SeqExp
               (ExpVar (Big (ast_to_string ast) ^ ".iter")
                :: List.map
                     (fn arity =>
                         LamExp
                           [(TuplePat [VarPat "others", VarPat "self"],
                             arity_to_exp_external ana srt bindings arity)])
                     aritys
                @ [TupleExp [ExpVar "others", ExpVar "self"]]))
      | BindingArity (binding, arity) =>
        arity_to_exp_external ana srt (binding :: bindings) arity
*)

fun map_binding_to_exp' f index binding =
    case binding of
        SortBinding srt =>
        f (srt, ExpVar (sort_to_string srt ^ "Var" ^ Int.toString (index ())))
      | SymbolBinding sym =>
        ExpVar (sym_to_string sym ^ Int.toString (index ()))
      | ProdBinding bindings =>
        TupleExp (List.map (map_binding_to_exp' f index) bindings)
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] => ExpVar (ast_to_string ast ^ Int.toString (index ()))
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
                                  [map_binding_to_exp binding f,
                                   TupleExp []])])
                        bindings
                   @ [TupleExp
                        [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                         TupleExp []]])])

and map_binding_to_exp binding f =
    let val index = ref 0
    in map_binding_to_exp' f (fn () => (index := !index + 1; !index)) binding
    end

fun map_arity_to_exp' f index arity =
    case arity of
        SortArity srt =>
        f (srt, ExpVar (sort_to_string srt ^ Int.toString (index ())))
      | SymbolArity sym =>
        ExpVar (sym_to_string sym ^ Int.toString (index ()))
      | ProdArity aritys =>
        TupleExp (List.map (map_arity_to_exp' f index) aritys)
      | AppArity (ast, aritys) =>
        (case aritys of
             [] => ExpVar (ast_to_string ast ^ Int.toString (index ()))
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
                        [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                         TupleExp []]])])
      | BindingArity (binding, arity) =>
        TupleExp
          [map_binding_to_exp' f index binding,
           map_arity_to_exp' f index arity]

and map_arity_to_exp arity f =
    let val index = ref 0
    in map_arity_to_exp' f (fn () => (index := !index + 1; !index)) arity
    end

fun extract_vars' index binding =
    case binding of
        SortBinding srt =>
        TupleExp
          [TupleExp [],
           ListExp [ExpVar (sort_to_string srt ^ Int.toString (index ()))]]
      | SymbolBinding sym =>
        TupleExp
          [TupleExp [],
           ListExp [ExpVar (sym_to_string sym ^ Int.toString (index ()))]]
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
      | AppBinding (ast, bindings) =>
        (case bindings of
             [] =>
             TupleExp
               [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                ListExp []]
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
                                      [VarPat "others",
                                       VarPat "self"],
                                    extract_vars binding)],
                                TupleExp
                                  [ExpVar "others",
                                   SeqExp
                                     [ExpVar "acc",
                                      ExpVar "@",
                                      ExpVar "self"]]))])
                        bindings
                @ [TupleExp
                     [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                      ListExp []]]))

and extract_vars binding =
    let val index = ref 0
    in extract_vars' (fn () => (index := !index + 1; !index)) binding
    end

fun arity_to_exp_split' (ana : ana) srt index arity =
    case arity of
        SortArity srt' =>
        ExpVar (sort_to_string srt' ^ Int.toString (index ()))
      | SymbolArity sym =>
        ExpVar (sym_to_string sym ^ Int.toString (index ()))
      | ProdArity aritys =>
        TupleExp
          (mapi
             (fn (i, arity) =>
                 ValDefn
                   (VarPat ("x" ^ Int.toString i ^ "'"),
                    arity_to_exp_split' ana srt index arity))
             aritys,
           TupleExp
             [TupleExp
                (mapi
                   (fn (i, _) =>
                       SeqExp [ExpVar "#1", ExpVar ("x" ^ Int.toString i ^ "'")])
                   aritys),
              SeqExp
                [ExpVar "List.concat",
                 ListExp
                   (mapi
                      (fn (i, _) =>
                          SeqExp [ExpVar "#2", ExpVar ("x" ^ Int.toString i ^ "'")])
                      aritys)]])
      | AppArity (ast, aritys) =>
        (case aritys of
             [] =>
             TupleExp
               [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                ListExp []]
           | _ =>
             SeqExp
               (ExpVar (Big (ast_to_string ast) ^ ".iter")
                :: List.map
                     (fn arity =>
                         LamExp
                           [(TuplePat [arity_to_pat arity, VarPat "acc"],
                             LetExp
                               ([ValDefn
                                   (TuplePat
                                      [VarPat "others",
                                       VarPat "self"],
                                    arity_to_exp_split ana srt arity)],
                                TupleExp
                                  [ExpVar "others",
                                   SeqExp
                                     [ExpVar "acc",
                                      ExpVar "@",
                                      ExpVar "self"]]))])
                        aritys
                @ [TupleExp
                     [ExpVar (ast_to_string ast ^ Int.toString (index ())),
                      ListExp []]]))
      | BindingArity (binding, arity) =>
        LetExp
          ([ValDefn
              (TuplePat [VarPat "skeleton", VarPat "varsandsyms"],
               extract_vars' index binding),
            ValDefn
              (TuplePat [VarPat "others", VarPat "self"],
               arity_to_exp_split' ana srt index arity)],
           TupleExp
             [TupleExp
                [ExpVar "skeleton",
                 (* ??? bind in here *) ExpVar "others"],
              SeqExp
                [ExpVar "List.map",
                 LamExp
                   [(VarPat (sort_to_string srt),
                     SeqExp
                       [ExpVar "List.foldl",
                        LamExp
                          [(TuplePat [VarPat "x", VarPat "acc"],
                            SeqExp
                              [ExpVar "Abt.into",
                               ExpVar
                                 (ops_name ana srt ^ "."
                                  ^ sort_to_string srt ^ "_oper_bind"),
                               SeqExp
                                 [ExpVar ("Abt.Binding"),
                                  TupleExp [ExpVar "x", ExpVar "acc"]]])],
                        ExpVar (sort_to_string srt),
                        ExpVar "varsandsyms"])],
                 ExpVar "self"]])

and arity_to_exp_split (ana : ana) srt arity =
    let val index = ref 0
    in arity_to_exp_split' ana srt (fn () => (index := !index + 1; !index)) arity
    end

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
                       (oper,
                        case arity_opt of
                            NONE => NONE
                          | SOME arity =>
                            SOME
                              (arity_to_type
                                 ana srt true
                                 (internalize_arity srt arity))))
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
                        NONE => (VarPat oper, ExpVar oper)
                      | SOME arity =>
                        (InjPat
                           (oper,
                            arity_to_pat (internalize_arity srt arity)),
                         SeqExp [ExpVar oper,
                                 map_arity_to_exp
                                   (internalize_arity srt arity)
                                   (fn (srt', exp) =>
                                       SeqExp
                                         (List.concat
                                            [[ExpVar ("Abt." ^ name),
                                              ExpVar
                                                (scoped_sort srt srt'
                                                 ^ "_oper_"
                                         ^ name)],
                                             List.map ExpVar args,
                                             [exp]]))]))
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
                     ModProj ("Variable", TypeVar "t"))]})
            (List.filter (#hasvar ana) (#mutual ana srt))

      val var_structure_defn =
          if #hasvar ana srt
          then [StructureDefn ("Var", NONE, StructVar "Variable")]
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
                 let
                   val oper_cases =
                       List.map
                         (fn (oper, arity_opt) =>
                             case arity_opt of
                                 NONE =>
                                 (VarPat oper,
                                  SeqExp
                                    [ExpVar "Abt.Oper",
                                     TupleExp
                                       [ExpVar (ops_name ana srt ^ "." ^ oper),
                                        ListExp []]])
                               | SOME arity =>
                                 (InjPat (oper, arity_to_pat arity),
                                  LetExp
                                    ([ValDefn
                                        (TuplePat
                                           [VarPat "others",
                                            VarPat "self"],
                                         arity_to_exp_split ana srt arity)],
                                     SeqExp
                                       [ExpVar "Abt.Oper",
                                        TupleExp
                                          [SeqExp
                                             [ExpVar
                                                (ops_name ana srt ^ "." ^ oper),
                                              ExpVar "others"],
                                           ExpVar "self"]])))
                         opers
                 in
                   if #hasvar ana srt
                   then
                     (InjPat ("Var", VarPat (sort_to_string srt ^ "Var")),
                      SeqExp
                        [ExpVar "Abt.Var",
                         ExpVar (sort_to_string srt ^ "Var")])
                     :: oper_cases
                   else oper_cases
                 end))]

      val view_out_code =
          FunDefn
            [("view_out",
              [VarPat "v"],
              NONE,
              CaseExp
                (ExpVar "v",
                 List.concat
                   [(if #hasvar ana srt
                     then
                       [(InjPat
                           ("Abt.Var",
                            VarPat (sort_to_string srt ^ "Var")),
                         SeqExp
                           [ExpVar "Var",
                            ExpVar (sort_to_string srt ^ "Var")])]
                     else []),
                    List.map
                      (fn (oper, arity_opt) =>
                          case arity_opt of
                              NONE =>
                              (InjPat
                                 ("Abt.Oper",
                                  TuplePat
                                    [VarPat (ops_name ana srt ^ "." ^ oper),
                                     ListPat []]),
                               ExpVar oper)
                            | SOME arity =>
                              (InjPat
                                 ("Abt.Oper",
                                  TuplePat
                                    [InjPat
                                       (ops_name ana srt ^ "." ^ oper,
                                        VarPat "others"),
                                     VarPat "self"]),
                               SeqExp
                                 [ExpVar oper,
                                  SeqExp
                                    [ExpVar "#1",
                                     arity_to_exp_external ana srt arity]]))
                      opers,
                    [(Wild,
                      SeqExp
                        [ExpVar "raise",
                         ExpVar "Fail",
                         StringExp "Internal Abbot Error"])]]))]

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

fun doit_impl (ana : ana) =
    let
      val external_ast_decls =
          mapfilter
            (fn (ast, (args, opers)) =>
                case opers of
                    [] => SOME (ast_decl ast args)
                  | _ => SOME (ast_decl ast args) (* ??? *))
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
                  | _ => (* ??? *)
                    SOME
                      (StructureDefn
                         (Big (ast_to_string ast),
                          NONE,
                          StructVar (Big (ast_to_string ast)))))
            (#asts ana)

      val internal_asts = [] (* ??? *)

      val symbols = create_symbol_structures (#symbs ana)

      val ops = List.map (create_mutual_ops ana) (#sorts ana)

      val sorts = List.concat
                     (List.map
                        (List.map (create_sort_structure_defn ana))
                        (#sorts ana))
      val defns =
          interleave BlankDefn
            (symbols @ external_ast_defns @ internal_asts @ ops @ sorts)
    in
      case external_ast_decls of
          [] =>
          Emit.emit
            [TLStructure
               ("Abbot",
                SOME (SigVar "ABBOT"),
                StructBody defns)]
        | _ =>
          Emit.emit
            [TLFunctor
               ("Abbot",
                external_ast_decls,
                SOME (SigVar "ABBOT"),
                StructBody defns)]
    end
end
