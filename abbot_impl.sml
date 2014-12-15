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

fun create_recursors
      {name : string,
       args : string list,
       sym_usef : symbol * EXP -> EXP,
       sort_usef : sort * EXP -> EXP,
       sym_bindingf : symbol * EXP -> EXP,
       sort_bindingf : sort * EXP -> EXP,
       prodf : EXP list -> EXP,
       listf : EXP -> EXP,
       extf : ext * EXP * (PAT * EXP) list -> EXP,
       abtf : abt -> EXP,
       dotf : EXP * EXP -> EXP,
       oper_patf : string * PAT option -> PAT,
       operf : string * EXP option -> EXP} =
    let
      val index =
          let val index = ref 0 in
            (fn str =>
                (index := !index + 1;
                 str ^ "'" ^ Int.toString (!index)))
          end

      val (create_abt_arity_rec, create_sort_arity_rec) =
          create_abt_and_sort_fun
            {sym_usef =
             fn sym =>
                let val str = index (sym_to_string sym)
                in (VarPat str, sym_usef (sym, ExpVar str))
                end,

             sort_usef =
             fn sort =>
                let val str = index (sort_to_string sort)
                in (VarPat str, sort_usef (sort, ExpVar str))
                end,

             sym_bindingf =
             fn sym =>
                let val str = index (sym_to_string sym)
                in (VarPat str, sym_bindingf (sym, ExpVar str))
                end,

             sort_bindingf =
             fn sort =>
                let val str = index (sort_to_string sort)
                in (VarPat str, sort_bindingf (sort, ExpVar str))
                end,

             prodf =
             fn patexps =>
                let val (pats, exps) = ListPair.unzip patexps
                in (TuplePat pats, prodf exps)
                end,

             listf =
             fn patexp =>
                let val str = index "list" in
                  (VarPat str,
                   listf
                     (SeqExp [ExpVar "List.map", LamExp [patexp], ExpVar str]))
                end,

             extf =
             fn (ext, patexps) =>
                let val str = index (ext_to_string ext)
                in (VarPat str, extf (ext, ExpVar str, patexps))
                end,

             abtf =
             fn (abt, patexps) =>
                let val str = index (abt_to_string abt) in
                  (VarPat str,
                   SeqExp
                     (abtf abt
                      :: List.map (fn patexp => LamExp [patexp]) patexps
                      @ List.map ExpVar args
                      @ [ExpVar str]))
                end,

             dotf =
             fn ((binding_pat, binding_exp), (arity_pat, arity_exp)) =>
                (TuplePat [binding_pat, arity_pat],
                 dotf (binding_exp, arity_exp))}
    in
      (fn (abt, abt_args, opers) =>
          let
            val abt_arg_names =
                StringTable.fromSeq
                  (StringTable.Seq.fromList
                     (List.map (fn arg => (arg, index arg)) abt_args))

            fun paramf str =
                let val str' = index str in
                  (VarPat str',
                   SeqExp
                     [ExpVar (valOf (StringTable.find abt_arg_names str)),
                      ExpVar str'])
                end
          in
            (name,
             List.map (VarPat o valOf o StringTable.find abt_arg_names) abt_args
             @ List.map VarPat args
             @ [VarPat (abt_to_string abt)],
             NONE,
             CaseExp
               (ExpVar (abt_to_string abt),
                List.map
                  (fn (oper, arity_opt) =>
                      case arity_opt of
                          NONE => (oper_patf (oper, NONE), operf (oper, NONE))
                        | SOME arity =>
                          let
                            val (arity_pat, arity_exp) =
                                create_abt_arity_rec paramf arity
                          in
                            (oper_patf (oper, SOME arity_pat),
                             operf (oper, SOME arity_exp))
                          end)
                  opers))
          end,
       fn (sort, opers) =>
          (name,
           List.map VarPat args @ [VarPat (sort_to_string sort)],
           NONE,
           CaseExp
             (ExpVar (sort_to_string sort),
              List.map
                (fn (oper, arity_opt) =>
                    case arity_opt of
                        NONE => (oper_patf (oper, NONE), operf (oper, NONE))
                      | SOME arity =>
                        let
                          val (arity_pat, arity_exp) =
                              create_sort_arity_rec arity
                        in
                          (oper_patf (oper, SOME arity_pat),
                           operf (oper, SOME arity_exp))
                        end)
                opers)))
    end

(*
(* Fix code duplication *)
fun create_abt_recursor
      {name : string,
       args : string list,
       sym_usef : symbol * EXP -> EXP,
       sort_usef : sort * EXP -> EXP,
       sym_bindingf : symbol * EXP -> EXP,
       sort_bindingf : sort * EXP -> EXP,
       prodf : EXP list -> EXP,
       listf : EXP -> EXP,
       extf : ext * EXP * (PAT * EXP) list -> EXP,
       abtf : abt -> EXP,
       oper_patf : string * PAT option -> PAT,
       operf : string * EXP option -> EXP}
      (abt, abt_args, opers)
    : string * PAT list * TYPE option * EXP =
    let
      open AbtArity

      val index =
          let val index = ref 0 in
            (fn str =>
                (index := !index + 1;
                 str ^ "'" ^ Int.toString (!index)))
          end

      val abt_arg_names =
          StringTable.fromSeq
            (StringTable.Seq.fromList
               (List.map (fn arg => (arg, index arg)) abt_args))

      fun create_abt_arity_rec arity : PAT * EXP =
          case arity of
              Param str =>
              let val str' = index str in
                (VarPat str',
                 SeqExp
                   [ExpVar (valOf (StringTable.find abt_arg_names str)),
                    ExpVar str'])
              end
            | SymbolUse sym =>
              let val str = index (sym_to_string sym)
              in (VarPat str, sym_usef (sym, ExpVar str))
              end
            | SortUse sort =>
              let val str = index (sort_to_string sort)
              in (VarPat str, sort_usef (sort, ExpVar str))
              end
            | SymbolBinding sym =>
              let val str = index (sym_to_string sym)
              in (VarPat str, sym_bindingf (sym, ExpVar str))
              end
            | SortBinding sort =>
              let val str = index (sort_to_string sort)
              in (VarPat str, sort_bindingf (sort, ExpVar str))
              end
            | Prod aritys =>
              let
                val (pats, exps) =
                    ListPair.unzip (List.map create_abt_arity_rec aritys)
              in
                (TuplePat pats, prodf exps)
              end
            | List arity =>
              let val str = index "list" in
                (VarPat str,
                 listf
                   (SeqExp
                      [ExpVar "List.map",
                       LamExp [create_abt_arity_rec arity],
                       ExpVar str]))
              end
            | AppExt (ext, aritys) =>
              let val str = index (ext_to_string ext) in
                (VarPat str,
                 extf (ext, ExpVar str, List.map create_abt_arity_rec aritys))
              end
            | AppAbt (abt, aritys) =>
              let val str = index (abt_to_string abt) in
                (VarPat str,
                 SeqExp
                   (abtf abt
                    :: List.map
                         (fn arity => LamExp [create_abt_arity_rec arity])
                         aritys
                    @ List.map ExpVar args
                    @ [ExpVar str]))
              end
    in
      (name,
       List.map (VarPat o valOf o StringTable.find abt_arg_names) abt_args
       @ List.map VarPat args
       @ [VarPat (abt_to_string abt)],
       NONE,
       CaseExp
         (ExpVar (abt_to_string abt),
          List.map
            (fn (oper, arity_opt) =>
                case arity_opt of
                    NONE => (oper_patf (oper, NONE), operf (oper, NONE))
                  | SOME arity =>
                    let val (arity_pat, arity_exp) = create_abt_arity_rec arity
                    in
                      (oper_patf (oper, SOME arity_pat),
                       operf (oper, SOME arity_exp))
                    end)
            opers))
    end

fun create_sort_recursor
      {name : string,
       args : string list,
       sym_usef : symbol * EXP -> EXP,
       sort_usef : sort * EXP -> EXP,
       sym_bindingf : symbol * EXP -> EXP,
       sort_bindingf : sort * EXP -> EXP,
       prodf : EXP list -> EXP,
       listf : EXP -> EXP,
       extf : ext * EXP * (PAT * EXP) list -> EXP,
       abtf : abt -> EXP,
       dotf : EXP * EXP -> EXP,
       oper_patf : string * PAT option -> PAT,
       operf : string * EXP option -> EXP}
      (sort, opers)
    : string * PAT list * TYPE option * EXP =
    let
      open SortArity

      val index =
          let val index = ref 0 in
            (fn str =>
                (index := !index + 1;
                 str ^ "'" ^ Int.toString (!index)))
          end

      fun create_sort_arity_rec arity : PAT * EXP =
          case arity of
              SymbolUse sym =>
              let val str = index (sym_to_string sym)
              in (VarPat str, sym_usef (sym, ExpVar str))
              end
            | SortUse sort =>
              let val str = index (sort_to_string sort)
              in (VarPat str, sort_usef (sort, ExpVar str))
              end
            | SymbolBinding sym =>
              let val str = index (sym_to_string sym)
              in (VarPat str, sym_bindingf (sym, ExpVar str))
              end
            | SortBinding sort =>
              let val str = index (sort_to_string sort)
              in (VarPat str, sort_bindingf (sort, ExpVar str))
              end
            | Prod aritys =>
              let
                val (pats, exps) =
                    ListPair.unzip (List.map create_sort_arity_rec aritys)
              in
                (TuplePat pats, prodf exps)
              end
            | List arity =>
              let val str = index "list" in
                (VarPat str,
                 listf
                   (SeqExp
                      [ExpVar "List.map",
                       LamExp [create_sort_arity_rec arity],
                       ExpVar str]))
              end
            | AppExt (ext, aritys) =>
              let val str = index (ext_to_string ext) in
                (VarPat str,
                 extf (ext, ExpVar str, List.map create_sort_arity_rec aritys))
              end
            | AppAbt (abt, aritys) =>
              let val str = index (abt_to_string abt) in
                (VarPat str,
                 SeqExp
                   (abtf abt
                    :: List.map
                         (fn arity => LamExp [create_sort_arity_rec arity])
                         aritys
                    @ List.map ExpVar args
                    @ [ExpVar str]))
              end
            | Dot (binding, arity) =>
              let
                val (binding_pat, binding_exp) = create_sort_arity_rec binding
                val (arity_pat, arity_exp) = create_sort_arity_rec arity
              in
                (TuplePat [binding_pat, arity_pat],
                 dotf (binding_exp, arity_exp))
              end
    in
      (name,
       List.map VarPat args @ [VarPat (sort_to_string sort)],
       NONE,
       CaseExp
         (ExpVar (sort_to_string sort),
          List.map
            (fn (oper, arity_opt) =>
                case arity_opt of
                    NONE => (oper_patf (oper, NONE), operf (oper, NONE))
                  | SOME arity =>
                    let val (arity_pat, arity_exp) = create_sort_arity_rec arity
                    in
                      (oper_patf (oper, SOME arity_pat),
                       operf (oper, SOME arity_exp))
                    end)
            opers))
    end
*)

val create_symbol_structures =
    List.map
      (fn sym =>
          StructureDefn
            (Big (sym_to_string sym),
             NONE,
             StructVar "Temp"))

local open AbtArity in
fun internalize_abt_arity arity =
    case arity of
        Param srt => Param srt
      | SortUse srt => SortUse srt
      | SymbolUse sym => SymbolUse sym
      | SortBinding _ => Prod []
      | SymbolBinding _ => Prod []
      | Prod aritys =>
        Prod (List.map internalize_abt_arity aritys)
      | List arity =>
        List (internalize_abt_arity arity)
      | AppExt (ext, aritys) =>
        AppExt (ext, List.map internalize_abt_arity aritys)
      | AppAbt (abt, aritys) =>
        AppAbt (abt, List.map internalize_abt_arity aritys)
      | Dot (binding, arity) =>
        Dot (internalize_abt_arity binding, internalize_abt_arity arity)
end

fun internalize_abt (abt, (args, opers)) =
    (abt,
     (args,
      List.map
        (fn (oper, arity_opt) =>
            (abt_to_string abt ^ "'" ^ oper,
             case arity_opt of
                NONE => NONE
              | SOME arity => SOME (internalize_abt_arity arity)))
        opers))

local open SortArity in
fun internalize_sort_arity arity =
    case arity of
        SortUse srt => SortUse srt
      | SymbolUse sym => SymbolUse sym
      | SortBinding _ => Prod []
      | SymbolBinding _ => Prod []
      | Prod aritys =>
        Prod (List.map internalize_sort_arity aritys)
      | List arity =>
        List (internalize_sort_arity arity)
      | AppExt (ext, aritys) =>
        AppExt (ext, List.map internalize_sort_arity aritys)
      | AppAbt (abt, aritys) =>
        AppAbt (abt, List.map internalize_sort_arity aritys)
      | Dot (binding, arity) =>
        Dot (internalize_sort_arity binding, internalize_sort_arity arity)
end

fun internalize_sort (sort, opers) =
    (sort,
     List.map
       (fn (oper, arity_opt) =>
           (sort_to_string sort ^ "'" ^ oper,
            case arity_opt of
                NONE => NONE
              | SOME arity => SOME (internalize_sort_arity arity)))
       opers)

fun create_mutual_ops (ana : ana) (abts, sorts) =
    let
(*??? should actualy use this or similar
      fun scoped_sort srt srt' =
          if #mutualwith ana srt srt'
          then sort_to_string srt'
          else ops_name ana srt' ^ "." ^ sort_to_string srt'
*)

      val abts = List.map internalize_abt abts
      val sorts = List.map internalize_sort sorts

      val abt_datatypes =
          List.map
            (fn (abt, (args, opers)) =>
                (abt_to_string abt,
                 List.map (fn arg => "'" ^ arg) args,
                 List.map
                   (fn (oper, arity_opt) =>
                       (oper,
                        case arity_opt of
                            NONE => NONE
                          | SOME arity =>
                            SOME (abt_arity_to_type ana true abt arity)))
                   opers))
            abts

      val sort_datatypes =
          List.map
            (fn (sort, opers) =>
                (sort_to_string sort ^ "_oper",
                 [],
                 List.map
                   (fn (oper, arity_opt) =>
                       (oper,
                        case arity_opt of
                            NONE => NONE
                          | SOME arity =>
                            SOME (sort_arity_to_type ana true sort arity)))
                   opers))
            sorts

      val withtypes =
          List.map
            (fn (sort, _) =>
                (sort_to_string sort,
                 [],
                 AppType
                   ([TypeVar (sort_to_string sort ^ "_oper")],
                    ModProjType ("Abt", TypeVar "t"))))
            sorts

      local
        val args = ["x", "i"]

        fun sym_usef name (sym, exp) =
            SeqExp
              [ExpVar ("Abt." ^ name),
               LamExp
                 [(VarPat "_",
                   LamExp
                     [(VarPat "_",
                       LamExp [(VarPat "t", ExpVar "t")])])],
               ExpVar "x",
               ExpVar "i",
               exp]

        fun sort_usef name abt_or_sort (sort, exp) =
            SeqExp
              [ExpVar ("Abt." ^ name),
               ExpVar
                 ((if #mutualwith ana abt_or_sort (Sort sort)
                   then sort_to_string sort
                   else
                     ops_name ana (Sort sort)
                     ^ "." ^ sort_to_string sort)
                  ^ "_oper_" ^ name),
               ExpVar "x",
               ExpVar "i",
               exp]

        val prodf = TupleExp

        fun extf (ext, exp, patexps) =
            case patexps of
                [] => exp
              | _ =>
                SeqExp
                  [ExpVar "#1",
                   SeqExp
                     (ExpVar (Big (ext_to_string ext) ^ ".iter")
                      :: List.map
                           (fn (pat, exp) =>
                               LamExp
                                 [(TuplePat [pat, TuplePat []],
                                   TupleExp [exp, TupleExp []])])
                           patexps
                      @ [TupleExp [exp, TupleExp []]])]

        fun abtf name abt_or_sort abt =
             if #mutualwith ana abt_or_sort (Abt abt)
             then ExpVar (abt_to_string abt ^ "_" ^ name)
             else
               ExpVar
                 (ops_name ana (Abt abt) ^ "."
                  ^ abt_to_string abt ^ "_" ^ name)

        fun oper_patf (oper, pat_opt) =
            case pat_opt of
                NONE => VarPat oper
              | SOME pat => InjPat (oper, pat)

        fun operf (oper, exp_opt) =
            case exp_opt of
                NONE => ExpVar oper
              | SOME exp => SeqExp [ExpVar oper, exp]

        fun invalid _ = raise Fail "Internal Abbot Error"
        fun ident l = l (* make these more global ??? *)

        fun recs name abt_or_sort =
            create_recursors
              {name =
               case abt_or_sort of
                   Abt abt => abt_to_string abt ^ "_" ^ name
                 | Sort sort => sort_to_string sort ^ "_oper_" ^ name,
               args = args,
               sym_usef = sym_usef name,
               sort_usef = sort_usef name abt_or_sort,
               sym_bindingf = invalid,
               sort_bindingf = invalid,
               prodf = TupleExp,
               listf = ident,
               extf = extf,
               abtf = abtf name abt_or_sort,
               dotf =
               fn (binding_exp, arity_exp) =>
                  TupleExp [binding_exp, arity_exp],
               oper_patf = oper_patf,
               operf = operf}
      in
      fun abt_rec name (abt, (abt_args, opers)) =
          #1 (recs name (Abt abt)) (abt, abt_args, opers)

      fun sort_rec name (sort, opers) =
          #2 (recs name (Sort sort)) (sort, opers)
      end
    in
      StructureDefn
        (String.concat
           (List.map (Big o abt_to_string o #1) abts
            @ List.map (Big o sort_to_string o #1) sorts)
         ^ "Ops",
         NONE,
         StructBody
           ([TypeDefns
               {datatypes = abt_datatypes @ sort_datatypes,
                aliases = withtypes},
             BlankDefn,
             FunDefns
               (List.map (abt_rec "bind") abts
                @ List.map (sort_rec "bind") sorts),
             BlankDefn,
             FunDefns
               (List.map (abt_rec "unbind") abts
                @ List.map (sort_rec "unbind") sorts)]))
    end

(* Code duplication??? *)
fun create_view_datatype_defn (ana : ana) (srt, opers) =
    let
      val oper_branches =
          List.map
            (fn (oper, arity_opt) =>
                (oper,
                 case arity_opt of
                     NONE => NONE
                   | SOME arity =>
                     SOME (sort_arity_to_type ana false srt arity)))
            opers

      val body =
          if #hasvar ana srt
          then ("Var", SOME (sort_to_var_type srt)) :: oper_branches
          else oper_branches
    in
      TypeDefns {datatypes = [("view", [], body)], aliases = []}
    end

fun bind_single oper_bind exp =
    TupleExp
      [SeqExp
         [ExpVar "List.foldl",
          LamExp
            [(TuplePat [VarPat "x", VarPat "acc"],
              SeqExp
                [ExpVar "Abt.into",
                 oper_bind,
                 SeqExp
                   [ExpVar ("Abt.Binding"),
                    TupleExp [ExpVar "x", ExpVar "acc"]]])],
          exp,
          ExpVar "vars"],
       ListExp []]

fun unbind_single oper_unbind exp =
    SeqExp
      [ExpVar "List.foldr",
       LamExp
         [(TuplePat [VarPat "x", VarPat "acc"],
           LetExp
             ([ValDefn
                 (InjPat ("Abt.Binding", TuplePat [VarPat "y", VarPat "acc'"]),
                  SeqExp
                    [ExpVar "Abt.out",
                     oper_unbind,
                     SeqExp
                       [ExpVar "Abt.unbind",
                        oper_unbind,
                        ExpVar "x",
                        ExpVar "~1", (* This violates every invariant... *)
                        ExpVar "acc"]])],
              ExpVar "acc'"))],
       exp,
       ExpVar "vars"]

fun view_in_code (ana : ana) abt_or_sort =
    create_recursors
      {name =
       case abt_or_sort of
           Abt abt => abt_to_string abt ^ "_view_in"
         | Sort _ => "view_in",

       args = ["vars"],

       sym_usef =
       fn (sym, exp) =>
          bind_single
            (LamExp
               [(VarPat "_",
                 LamExp
                   [(VarPat "_",
                     LamExp [(VarPat "t", ExpVar "t")])])])
            (SeqExp
               [ExpVar "Abt.into",
                LamExp
                  [(VarPat "_",
                    LamExp
                      [(VarPat "_",
                        LamExp [(VarPat "t", ExpVar "t")])])],
                SeqExp [ExpVar "Abt.Var", exp]]),

       sort_usef =
       fn (sort, exp) =>
          bind_single
            (ExpVar
               (ops_name ana (Sort sort) ^ "."
                ^ sort_to_string sort ^ "_oper_bind"))
            exp,

       sym_bindingf =
       fn (sym, exp) =>
          TupleExp [TupleExp [], ListExp [exp]],

       sort_bindingf =
       fn (sort, exp) =>
          TupleExp [TupleExp [], ListExp [exp]],

       prodf =
       fn exps =>
          let
            val (val_decls, ts, vars) =
                unzip3
                  (mapi
                     (fn (i, exp) =>
                         (ValDefn
                            (TuplePat
                               [VarPat ("t" ^ Int.toString i),
                                VarPat ("vars'" ^ Int.toString i)],
                             exp),
                          ExpVar ("t" ^ Int.toString i),
                          ExpVar ("vars'" ^ Int.toString i)))
                     exps)
          in
            (LetExp
               (val_decls,
                TupleExp
                  [TupleExp ts,
                   SeqExp (interleave (ExpVar "@") vars)]))
          end,

       listf =
       fn exp =>
          LetExp
            ([ValDefn
                (TuplePat [VarPat "ts", VarPat "vars'"],
                 SeqExp [ExpVar "ListPair.unzip", exp])],
             TupleExp
               [ExpVar "ts",
                SeqExp [ExpVar "List.concat", ExpVar "vars'"]]),

       extf =
       fn (ext, exp, patexps) =>
          case patexps of
              [] => TupleExp [exp, ListExp []]
            | _ =>
              SeqExp
                (ExpVar (Big (ext_to_string ext) ^ ".iter")
                 :: List.map
                      (fn (pat, exp) =>
                          LamExp
                            [(TuplePat [pat, VarPat "vars'"],
                              LetExp
                                ([ValDefn
                                    (TuplePat [VarPat "t", VarPat "vars''"],
                                     exp)],
                                 TupleExp
                                   [ExpVar "t",
                                    SeqExp
                                      [ExpVar "vars''",
                                       ExpVar "@",
                                       ExpVar "vars'"]]))])
                      patexps
                 @ [TupleExp [exp, ListExp []]]),

       abtf = fn abt => ExpVar (abt_to_string abt ^ "_view_in"),

       dotf =
       fn (binding_exp, arity_exp) =>
          LetExp
            ([ValDefn
                (TuplePat [VarPat "t", VarPat "vars'"],
                 binding_exp),
              ValDefn
                (VarPat "vars",
                 SeqExp [ExpVar "vars'", ExpVar "@", ExpVar "vars"]),
              ValDefn
                (TuplePat [VarPat "t'", VarPat "vars'"],
                 arity_exp)],
             TupleExp
               [TupleExp [ExpVar "t", ExpVar "t'"],
                ExpVar "vars'"]),

       oper_patf =
       fn (oper, pat_opt) =>
          case pat_opt of
              NONE => VarPat oper
            | SOME pat => InjPat (oper, pat),

       operf =
       case abt_or_sort of
           Abt abt =>
           (fn (oper, exp_opt) =>
               case exp_opt of
                   NONE =>
                   TupleExp
                     [ExpVar
                        (ops_name ana (Abt abt) ^ "."
                         ^ abt_to_string abt ^ "'" ^ oper),
                      ListExp []]
                 | SOME exp =>
                   LetExp
                     ([ValDefn (TuplePat [VarPat "t", VarPat "vars'"], exp)],
                      TupleExp
                        [SeqExp
                           [ExpVar
                              (ops_name ana (Abt abt) ^ "."
                               ^ abt_to_string abt ^ "'" ^ oper),
                            ExpVar "t"],
                         ExpVar "vars'"]))
         | Sort sort =>
           (fn (oper, exp_opt) =>
               case exp_opt of
                   NONE =>
                   SeqExp
                     [ExpVar "Abt.Oper",
                      ExpVar
                        (ops_name ana (Sort sort) ^ "."
                         ^ sort_to_string sort ^ "'" ^ oper)]
                 | SOME exp =>
                   SeqExp
                     [ExpVar "Abt.Oper",
                      SeqExp
                        [ExpVar
                           (ops_name ana (Sort sort) ^ "."
                            ^ sort_to_string sort ^ "'" ^ oper),
                         SeqExp [ExpVar "#1", exp]]])}

fun view_out_code (ana : ana) abt_or_sort =
    create_recursors
      {name =
       case abt_or_sort of
           Abt abt => abt_to_string abt ^ "_view_out"
         | Sort _ => "oper_view_out",

       args = ["vars"],

       sym_usef =
       fn (sym, exp) =>
          (LetExp
             ([ValDefn
                 (InjPat ("Abt.Var", VarPat "t"),
                  SeqExp
                    [ExpVar "Abt.out",
                     LamExp
                       [(VarPat "_",
                         LamExp
                           [(VarPat "_",
                             LamExp [(VarPat "t", ExpVar "t")])])],
                     unbind_single
                       (LamExp
                          [(VarPat "_",
                            LamExp
                              [(VarPat "_",
                                LamExp [(VarPat "t", ExpVar "t")])])])
                       exp])],
              TupleExp [ExpVar "t", ListExp []])),

       sort_usef =
       fn (sort, exp) =>
          TupleExp
            [unbind_single
               (ExpVar
                  (ops_name ana (Sort sort) ^ "."
                   ^ sort_to_string sort ^ "_oper_unbind"))
               exp,
             ListExp []],

       sym_bindingf =
       fn (sym, exp) =>
          LetExp
            ([ValDefn (VarPat "x", SeqExp [ExpVar "Temp.new", StringExp "x"])],
             TupleExp [ExpVar "x", ListExp [ExpVar "x"]]),

       sort_bindingf =
       fn (sort, exp) =>
          LetExp
            ([ValDefn (VarPat "x", SeqExp [ExpVar "Temp.new", StringExp "x"])],
             TupleExp [ExpVar "x", ListExp [ExpVar "x"]]),

       prodf =
       fn exps =>
          let
            val (val_decls, ts, vars) =
                unzip3
                  (mapi
                     (fn (i, exp) =>
                         (ValDefn
                            (TuplePat
                               [VarPat ("t" ^ Int.toString i),
                                VarPat ("vars'" ^ Int.toString i)],
                             exp),
                          ExpVar ("t" ^ Int.toString i),
                          ExpVar ("vars'" ^ Int.toString i)))
                     exps)
          in
            (LetExp
               (val_decls,
                TupleExp
                  [TupleExp ts,
                   SeqExp (interleave (ExpVar "@") vars)]))
          end,

       listf =
       fn exp =>
          LetExp
            ([ValDefn
                (TuplePat [VarPat "ts", VarPat "vars'"],
                 SeqExp [ExpVar "ListPair.unzip", exp])],
             TupleExp
               [ExpVar "ts",
                SeqExp [ExpVar "List.concat", ExpVar "vars'"]]),

       abtf = fn abt => ExpVar (abt_to_string abt ^ "_view_out"),

       extf =
       fn (ext, exp, patexps) =>
          case patexps of
              [] => TupleExp [exp, ListExp []]
            | _ =>
              SeqExp
                (ExpVar (Big (ext_to_string ext) ^ ".iter")
                 :: List.map
                      (fn (pat, exp) =>
                          LamExp
                            [(TuplePat [pat, VarPat "vars'"],
                              LetExp
                                ([ValDefn
                                    (TuplePat [VarPat "t", VarPat "vars''"],
                                     exp)],
                                 TupleExp
                                   [ExpVar "t",
                                    SeqExp
                                      [ExpVar "vars''",
                                       ExpVar "@",
                                       ExpVar "vars'"]]))])
                      patexps
                 @ [TupleExp [exp, ListExp []]]),

       dotf =
       fn (binding_exp, arity_exp) =>
          LetExp
            ([ValDefn
                (TuplePat [VarPat "t", VarPat "vars'"],
                 binding_exp),
              ValDefn
                (VarPat "vars",
                 SeqExp [ExpVar "vars'", ExpVar "@", ExpVar "vars"]),
              ValDefn
                (TuplePat [VarPat "t'", VarPat "vars'"],
                 arity_exp)],
             TupleExp
               [TupleExp [ExpVar "t", ExpVar "t'"],
                ExpVar "vars'"]),

       oper_patf =
       fn (oper, pat_opt) =>
          case pat_opt of
              NONE =>
              VarPat
                (ops_name ana abt_or_sort ^ "."
                 ^ abt_or_sort_to_string abt_or_sort ^ "'" ^ oper)
            | SOME pat =>
              InjPat
                (ops_name ana abt_or_sort ^ "."
                 ^ abt_or_sort_to_string abt_or_sort ^ "'" ^ oper,
                 pat),

       operf =
       case abt_or_sort of
           Abt _ =>
           (fn (oper, exp_opt) =>
               case exp_opt of
                   NONE =>
                   TupleExp [ExpVar oper, ListExp []]
                 | SOME exp =>
                   LetExp
                     ([ValDefn (TuplePat [VarPat "t", VarPat "vars'"], exp)],
                      TupleExp
                        [SeqExp [ExpVar oper, ExpVar "t"],
                         ExpVar "vars'"]))
         | Sort _ =>
           (fn (oper, exp_opt) =>
               case exp_opt of
                   NONE => ExpVar oper
                 | SOME exp =>
                   SeqExp [ExpVar oper, SeqExp [ExpVar "#1", exp]])}

fun create_mutual_abt_view_datatype ana abts =
    case abts of
        [] => []
      | (abt, _)::_ =>
        concatWith [BlankDefn]
          [List.map TypeDefns (#2 (create_mutual_types ana (Abt abt))),
           [TypeDefns
              {datatypes=List.map (abt_datatype ana) abts,
               aliases=[]},
            BlankDefn,
            FunDefns
              (List.map
                 (fn (abt, (args, opers)) =>
                     #1 (view_in_code ana (Abt abt)) (abt, args, opers))
                 abts),
            FunDefns
              (List.map
                 (fn (abt, (args, opers)) =>
                     #1 (view_out_code ana (Abt abt)) (abt, args, opers))
                 abts)]]

fun create_abt_structure_defn ana (abt, (args, opers)) =
    StructureDefn
      (Big (abt_to_string abt),
       NONE,
       StructBody
         (concatWith [BlankDefn]
            [List.map TypeDefns (op@ (create_mutual_types ana (Abt abt))),
             [DatatypeCopy (abt_to_string abt, TypeVar (abt_to_string abt)),
              BlankDefn,
              TypeDefns
                {aliases = [("t", args, TypeVar (abt_to_string abt))],
                 datatypes = []}]]))

fun create_sort_structure_defn (ana : ana) (sort, opers) =
    let
      val var_structure_defn =
          if #hasvar ana sort
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
            if #hasvar ana sort
            then
              ValDefn
                (VarPat "Var'",
                 SeqExp [ExpVar "into", ExpVar "o", ExpVar "Var"])
              :: oper_constructors
            else oper_constructors
          end

      val view_in_code =
          let
            val (name, args, typ, CaseExp (exp, cases)) = (* This is ugly ??? *)
                #2 (view_in_code ana (Sort sort)) (sort, opers)
          in
            if #hasvar ana sort
            then
              (name, args, typ,
               CaseExp
                 (exp,
                  (InjPat ("Var", VarPat "x"),
                   SeqExp [ExpVar "Abt.Var", ExpVar "x"])
                  :: cases))
            else (name, args, typ, CaseExp (exp, cases))
          end

      val oper_view_out_code =
          #2 (view_out_code ana (Sort sort)) (sort, opers)

      val view_out_code =
          FunDefns
            [("view_out",
              [VarPat "t"],
              NONE,
              CaseExp
                (ExpVar "t",
                 (if #hasvar ana sort
                  then
                    [(InjPat ("Abt.Var", VarPat "x"),
                      SeqExp [ExpVar "Var", ExpVar "x"])]
                  else [])
                 @ [(InjPat ("Abt.Oper", VarPat "oper"),
                      SeqExp [ExpVar "oper_view_out", ListExp [], ExpVar "oper"]),
                     (Wild,
                      SeqExp
                        [ExpVar "raise",
                         ExpVar "Fail",
                         StringExp "Internal Abbot Error"])]))]

      val into_code =
          FunDefns
            [("into",
              [VarPat "v"],
              NONE,
              SeqExp
                [ExpVar "Abt.into",
                 ExpVar
                   (ops_name ana (Sort sort)
                    ^ "." ^ sort_to_string sort ^ "_oper_bind"),
                 SeqExp [ExpVar "view_in", ListExp [], ExpVar "v"]])]

      val out_code =
          FunDefns
            [("out",
              [VarPat (sort_to_string sort)],
              NONE,
              SeqExp
                [ExpVar "view_out",
                 SeqExp
                   [ExpVar "Abt.out",
                    ExpVar
                      (ops_name ana (Sort sort)
                       ^ "." ^ sort_to_string sort ^ "_oper_unbind"),
                    ExpVar (sort_to_string sort)]])]

      val aequiv_code =
          FunDefns
            [("aequiv",
              [TuplePat [VarPat "l", VarPat "r"]],
              NONE,
              SeqExp
                [ExpVar "raise",
                 ExpVar "Fail",
                 StringExp "Unimpl"])]

      val toString_code =
          FunDefns
            [("toString",
              [VarPat (sort_to_string sort)],
              NONE,
              SeqExp
                [ExpVar "raise",
                 ExpVar "Fail",
                 StringExp "Unimpl"])]

      val substitutions =
          List.map
            (fn sort' =>
                FunDefns
                  [(if sort = sort'
                    then "subst"
                    else "subst" ^ Big (sort_to_string sort'),
                    [VarPat (sort_to_string sort' ^ "1"),
                     VarPat "x",
                     VarPat (sort_to_string sort ^ "2")],
                    NONE,
                    SeqExp [ExpVar "raise", ExpVar "Fail", StringExp "Unimpl"])])
            (List.filter (#hasvar ana) (#2 (#dependencies ana (Sort sort))))

      val all_defns =
          List.concat
            [List.map TypeDefns (op@ (create_mutual_types ana (Sort sort))),
             [TypeDefns
                {datatypes = [],
                 aliases =
                 [(sort_to_string sort,
                   [],
                   ModProjType
                     (ops_name ana (Sort sort),
                      TypeVar (sort_to_string sort)))]},
              TypeDefns
                {datatypes = [],
                 aliases = [("t", [], sort_to_type sort)]},
              BlankDefn],
             var_structure_defn,
             [BlankDefn,
              create_view_datatype_defn ana (sort, opers),
              BlankDefn,
              FunDefns [view_in_code],
              BlankDefn,
              FunDefns [oper_view_out_code],
              BlankDefn,
              view_out_code,
              BlankDefn,
              into_code,
              out_code,
              aequiv_code,
              toString_code],
             (case substitutions of
                  [] => []
                | _ => BlankDefn :: substitutions),
             [BlankDefn],
             convenient_contructors]
    in
      StructureDefn (Big (sort_to_string sort), NONE, StructBody all_defns)
    end

fun doit_impl sig_name struct_name (ana : ana) =
    let
      val external_decls =
          List.map
            (fn (ext, args) =>
                StructureDecl
                  (Big (ext_to_string ext),
                   create_ext_signature args))
            (#externals ana)

      val external_defns =
          List.map
            (fn (ext, _) =>
                StructureDefn
                  (Big (ext_to_string ext),
                   NONE,
                   StructVar (Big (ext_to_string ext))))
            (#externals ana)

      val symbols = create_symbol_structures (#symbols ana)

      val abts_and_sorts =
          List.concat
            (List.map
               (fn mutual =>
                   let
                     val (abts, sorts) =
                         List.partition
                           (fn Sum2.In1 _ => true
                           | Sum2.In2 _ => false)
                           mutual

                     val abts = List.map (fn Sum2.In1 x => x) abts
                     val sorts = List.map (fn Sum2.In2 x => x) sorts
                   in
                     create_mutual_ops ana (abts, sorts)
                     :: create_mutual_abt_view_datatype ana abts
                     @ List.map (create_abt_structure_defn ana) abts
                     @ List.map (create_sort_structure_defn ana) sorts
                   end)
               (#abts_and_sorts ana))

      val defns =
          symbols
          @ [BlankDefn]
          @ interleave BlankDefn (external_defns @ abts_and_sorts)

      val sig_with_where_types =
          List.foldl
            (fn ((ext, args), acc) =>
                WhereType
                  (acc,
                   AppType
                     (List.map (fn arg => TypeVar ("'" ^ arg)) args,
                      ModProjType (Big (ext_to_string ext), TypeVar "t")),
                   AppType
                     (List.map (fn arg => TypeVar ("'" ^ arg)) args,
                      ModProjType (Big (ext_to_string ext), TypeVar "t"))))
            (SigVar sig_name)
            (#externals ana)
    in
      case external_decls of
          [] =>
          Emit.emit
            [TLStructure
               (struct_name,
                SOME sig_with_where_types,
                StructBody defns)]
        | _ =>
          Emit.emit
            [TLFunctor
               (struct_name,
                external_decls,
                SOME sig_with_where_types,
                StructBody defns)]
    end
end
