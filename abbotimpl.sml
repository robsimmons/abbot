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
            (Big sym,
             NONE,
             StructVar "Symbol"))

fun oper_to_pat_external (ana : ana) srt oper =
    case #arity ana srt oper of
        [] => VarPat oper
      | arity =>
        let
          val pats =
              mapi
                (fn (i, (_, srt')) =>
                    VarPat (srt' ^ Int.toString i))
                arity
        in
          InjPat (oper, TuplePat pats)
        end

fun oper_to_pat_internal (ana : ana) srt oper =
    case List.filter (fn (_, srt') => srt <> srt') (#arity ana srt oper) of
        [] => VarPat oper
      | arity =>
        let
          val pats =
              mapi
                (fn (i, (_, srt')) =>
                    VarPat (srt' ^ Int.toString i))
                arity
        in
          InjPat (oper, TuplePat pats)
        end

fun oper_to_pat_split (ana : ana) srt oper =
    let
      val with_indices =
          mapi (fn x => x) (#arity ana srt oper)

      val (self, others) =
          List.partition (fn (_, (_, srt')) => srt = srt') with_indices

      val self_pats =
          List.map
            (fn (i, (_, srt')) =>
                VarPat (srt' ^ Int.toString i))
            self

      val other_pats =
          List.map
            (fn (i, (_, srt')) =>
                VarPat (srt' ^ Int.toString i))
            others
    in
      InjPat
        ("Abt.Oper",
         TuplePat
           [(case other_pats of
                 [] => VarPat (ops_name ana srt ^ "." ^ oper)
               | _ => InjPat (ops_name ana srt ^ "." ^ oper, TuplePat other_pats)),
            ListPat self_pats])
    end

fun oper_to_exp_external (ana : ana) srt oper =
    case #arity ana srt oper of
        [] => ([], ExpVar oper)
      | arity =>
        let
          val (bounds, exps) =
              ListPair.unzip
                (mapi
                   (fn (i, (bound, srt')) =>
                       ((i, bound, srt'),
                        mapi
                          (fn (j, srt'') =>
                              ExpVar
                                (srt'' ^ Int.toString i
                                 ^ "v" ^ Int.toString j))
                          bound
                        @ [ExpVar (srt' ^ Int.toString i)]))
                   arity)
        in
          (bounds, SeqExp [ExpVar oper, TupleExp (List.map TupleExp exps)])
        end

fun map_oper_to_exp_internal (ana : ana) srt oper f =
    case List.filter (fn (_, srt') => srt <> srt') (#arity ana srt oper) of
        [] => ExpVar oper
      | arity =>
        let
          val exps =
              mapi
                (fn (i, (bound, srt')) =>
                    f (srt', ExpVar (srt' ^ Int.toString i)))
                arity
        in
          SeqExp [ExpVar oper, TupleExp exps]
        end

fun oper_to_exp_split (ana : ana) srt oper =
    let
      val with_indices =
          mapi (fn x => x) (#arity ana srt oper)

      val (self, other) =
          List.partition (fn (_, (_, srt')) => srt = srt') with_indices

      fun bind_vars (i, (bound, srt)) =
          List.foldr (* ??? foldl or foldr *)
            (fn (srt', exp) =>
                let
                  val srt_or_sym =
                      if #issym ana srt'
                      then "Sym"
                      else "Var"
                in
                  SeqExp
                    [ExpVar "Abt.into",
                     ExpVar (ops_name ana srt ^ "." ^ srt ^ "_oper_bind_var"),
                     ExpVar (ops_name ana srt ^ "." ^ srt ^ "_oper_bind_sym"),
                     SeqExp
                       [ExpVar ("Abt." ^ srt_or_sym ^ "Binding"),
                        exp]]
                end)
            (ExpVar (srt ^ Int.toString i))
            bound

      val self_exps = List.map bind_vars self

      val other_exps = List.map bind_vars other
    in
      SeqExp
        [ExpVar "Abt.Oper",
         TupleExp
           [(case other_exps of
                 [] => ExpVar (ops_name ana srt ^ "." ^ oper)
               | _ => SeqExp [ExpVar (ops_name ana srt ^ "." ^ oper), TupleExp other_exps]),
            ListExp self_exps]]
    end

fun create_mutual_ops (ana : ana) srts =
    let
      fun scoped_sort srt srt' =
          if #issym ana srt'
          then Big srt' ^ ".t"
          else if #mutualwith ana srt srt'
          then srt'
          else String.concat (List.map Big (#mutual ana srt')) ^ "Ops." ^ srt'

      val datatypes =
          List.map
            (fn srt =>
                (srt ^ "_oper",
                 [],
                 List.map
                   (fn oper => (oper, aritys_to_type_internal ana srt oper true))
                   (#opers ana srt)))
            srts

      val withtypes =
          List.map
            (fn srt =>
                (srt,
                 [],
                 App
                   ([TypeVar (srt ^ "_oper")],
                    ModProj ("Abt", TypeVar "t"))))
            srts

      fun oper_rec name args srt =
          (srt ^ "_oper_" ^ name,
           List.map VarPat args @ [VarPat srt],
           NONE,
           CaseExp
             (ExpVar srt,
              List.map
                (fn oper =>
                    (oper_to_pat_internal ana srt oper,
                     map_oper_to_exp_internal ana srt oper
                       (fn (srt', exp) =>
                           if #issym ana srt'
                           then exp
                           else
                             SeqExp
                               (List.concat
                                  [[ExpVar ("Abt." ^ name),
                                    ExpVar
                                      (scoped_sort srt srt'
                                       ^ "_oper_"
                                       ^ name)],
                                   List.map ExpVar args,
                                   [exp]]))))
                (#opers ana srt)))

      fun aequiv_code srt =
          (srt ^ "_oper_aequiv",
           [TuplePat [VarPat "l", VarPat "r"]],
           NONE,
           SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])

      fun toString_code srt =
          (srt ^ "_oper_toString",
           [VarPat srt],
           NONE,
           SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])
    in
      StructureDefn
        (String.concat (List.map Big srts) ^ "Ops",
         NONE,
         StructBody
           ([TypeDefns {datatypes = datatypes, aliases = withtypes},
             FunDefn (List.map (oper_rec "bind_var" ["x", "i"]) srts),
             FunDefn (List.map (oper_rec "unbind_var" ["x", "i"]) srts),
             FunDefn (List.map (oper_rec "bind_sym" ["a", "i"]) srts),
             FunDefn (List.map (oper_rec "unbind_sym" ["a", "i"]) srts),
             FunDefn (List.map aequiv_code srts),
             FunDefn (List.map toString_code srts)]))
    end

(* Code duplication??? *)
fun create_view_datatype_defn ana srt =
    let
      val args = List.map (fn srt => "'" ^ srt) (#mutual ana srt)

      val oper_branches =
          List.map
            (fn oper =>
                (oper,
                 aritys_to_type_external ana srt oper false))
            (#opers ana srt)

      val body =
          if List.exists (fn x => x = srt) (#varin ana srt)
          then ("Var", SOME (TypeVar (srt ^ "Var"))) :: oper_branches
          else oper_branches
    in
      TypeDefns {datatypes = [("view", args, body)], aliases = []}
    end

fun create_sort_structure_defn (ana : ana) srt =
    let
      val mutual_type_defns =
          let val srts = #mutual ana srt in
            List.map
              (fn srt =>
                  TypeDefns
                    {datatypes = [],
                     aliases =
                     [(srt,
                       [],
                       ModProj
                         (String.concat (List.map Big srts) ^ "Ops",
                          TypeVar srt))]})
              srts
          end

      val mutual_var_defns =
          List.concat
            (List.map
               (fn var_srt =>
                   if #mutualwith ana srt var_srt
                   then
                     [TypeDefns
                        {datatypes = [],
                         aliases =
                         [(var_srt ^ "Var",
                           [],
                           ModProj ("Variable", TypeVar "t"))]}]
                   else [])
               (#varin ana srt))

      val var_structure_defn =
          if List.exists (fn x => x = srt) (#varin ana srt)
          then [StructureDefn ("Var", NONE, StructVar "Variable")]
          else []

      val convenient_contructors =
          let
            val oper_constructors =
                List.map
                  (fn oper =>
                      ValDefn
                        (VarPat (oper ^ "'"),
                         (case #arity ana srt oper of
                              [] => SeqExp [ExpVar "into", ExpVar oper]
                            | _ =>
                              SeqExp
                                [ExpVar "into", ExpVar "o", ExpVar oper])))
                  (#opers ana srt)
          in
            if List.exists (fn x => x = srt) (#varin ana srt)
            then
              ValDefn
                (VarPat "Var'",
                 SeqExp [ExpVar "into", ExpVar "o", ExpVar "Var"])
              :: oper_constructors
            else oper_constructors
          end

      val view_in_code = (* Var case ??? *)
          FunDefn
            [("view_in",
              [VarPat "v"],
              NONE,
              CaseExp
                (ExpVar "v",
                 List.map
                   (fn oper =>
                       (oper_to_pat_external ana srt oper,
                        oper_to_exp_split ana srt oper))
                   (#opers ana srt)))]

      val view_out_code =
          FunDefn
            [("view_out",
              [VarPat "v"],
              NONE,
              CaseExp
                (ExpVar "v",
                 List.map
                   (fn oper =>
                       (oper_to_pat_split ana srt oper,
                        let
                          val (bounds, exp) =
                              oper_to_exp_external ana srt oper
                        in
                          LetExp
                            (List.concat
                               (List.map
                                  (fn (i, bound, srt') =>
                                      mapi
                                        (fn (j, srt'') =>
                                            ValDefn
                                              (InjPat
                                                 ("Abt."
                                                  ^ (if #issym ana srt''
                                                     then "Sym"
                                                     else "Var")
                                                  ^ "Binding",
                                                  TuplePat
                                                    [VarPat
                                                       (srt'' ^ Int.toString i
                                                        ^ "v" ^ Int.toString j),
                                                     VarPat (srt' ^ Int.toString i)]),
                                               SeqExp
                                                 [ExpVar "Abt.out",
                                                  ExpVar
                                                    (ops_name ana srt'
                                                     ^ "."
                                                     ^ srt'
                                                     ^ "_oper_unbind_var"),
                                                  ExpVar
                                                    (ops_name ana srt'
                                                     ^ "."
                                                     ^ srt'
                                                     ^ "_oper_unbind_sym"),
                                                  ExpVar (srt' ^ Int.toString i)]))
                                        bound)
                                  bounds),
                             exp)
                        end))
                   (#opers ana srt)))]

      val into_code =
          FunDefn
            [("into",
              [VarPat "v"],
              NONE,
              SeqExp
                [ExpVar "Abt.into",
                 ExpVar
                   (ops_name ana srt
                    ^ "." ^ srt ^ "_oper_bind_var"),
                 ExpVar
                  (ops_name ana srt
                   ^ "." ^ srt ^ "_oper_bind_sym"),
                 SeqExp [ExpVar "view_in", ExpVar "v"]])]

      val out_code =
          FunDefn
            [("out",
              [VarPat srt],
              NONE,
              SeqExp
                [ExpVar "view_out",
                 SeqExp
                   [ExpVar "Abt.out",
                    ExpVar
                      (String.concat (List.map Big (#mutual ana srt))
                       ^ "Ops." ^ srt ^ "_oper_unbind_var"),
                    ExpVar
                      (String.concat (List.map Big (#mutual ana srt))
                       ^ "Ops." ^ srt ^ "_oper_unbind_sym"),
                    ExpVar srt]])]

      val aequiv_code =
          FunDefn
            [("aequiv",
              [TuplePat [VarPat "l", VarPat "r"]],
              NONE,
              SeqExp
                [ExpVar "Abt.aequiv",
                 ExpVar
                   (String.concat (List.map Big (#mutual ana srt))
                    ^ "Ops." ^ srt ^ "_oper_aequiv"), (* ???Code duplication *)
                 TupleExp [ExpVar "l", ExpVar "r"]])]

      val toString_code =
          FunDefn
            [("toString",
              [VarPat srt],
              NONE,
              SeqExp
                [ExpVar "Abt.toString",
                 ExpVar
                   (String.concat (List.map Big (#mutual ana srt))
                    ^ "Ops." ^ srt ^ "_oper_toString"), (* ???Code duplication *)
                 ExpVar srt])]

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
                    else "subst" ^ Big srt',
                    [VarPat (srt' ^ "1"),
                     VarPat "x",
                     VarPat (srt ^ "2")],
                    NONE,
                    SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])])
            (#varin ana srt)

      val all_defns =
          List.concat
            [mutual_type_defns,
             [TypeDefns
                {datatypes = [],
                 aliases = [("t", [], TypeVar srt)]}],
             mutual_var_defns,
             [BlankDefn],
             var_structure_defn,
             [BlankDefn],
             [create_view_datatype_defn ana srt],
             [BlankDefn],
             [view_in_code,
              view_out_code,
              into_code,
              out_code,
              aequiv_code,
              toString_code,
              map_code],
             (case substitutions of [] => [] | _ => BlankDefn :: substitutions),
             [BlankDefn],
             convenient_contructors]
    in
      StructureDefn (Big srt, NONE, StructBody all_defns)
    end

fun doit_impl (ana : ana) =
    Emit.emit
      [TLStructure
         ("Abbot",
          SOME (SigVar "ABBOT"),
          StructBody
            (interleave BlankDefn
               (List.concat
                  [create_symbol_structures (#symbs ana),
                   List.map (create_mutual_ops ana) (#sorts ana),
                   List.concat
                     (List.map
                        (List.map (create_sort_structure_defn ana))
                        (#sorts ana))])))]
end
