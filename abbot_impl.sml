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
             NONE : TYPE option,
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
           NONE : TYPE option,
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

val create_symbol_structures =
    List.map
      (fn sym =>
          StructureDefn
            (Big (sym_to_string sym),
             NONE,
             StructVar "Temp"))


fun internal_oper abt_or_sort oper =
    Big (abt_or_sort_to_string abt_or_sort) ^ "'" ^ oper

local
  fun aequiv_code (ana : ana) abt_or_sort internal_abt =
      let
        val index =
            let val index = ref 0 in
              (fn str =>
                  (index := !index + 1;
                   str ^ "'" ^ Int.toString (!index)))
            end
      in
        create_abt_and_sort_fun
          {sym_usef =
           fn sym =>
              let
                val str1 = index (sym_to_string sym)
                val str2 = index (sym_to_string sym)
              in
                (VarPat str1,
                 VarPat str2,
                 SeqExp
                   [ExpVar "Abt.aequiv",
                    LamExp [(Wild, ExpVar "true")],
                    TupleExp [ExpVar str1, ExpVar str2]])
              end,
           sort_usef =
           fn sort =>
              let
                val str1 = index (sort_to_string sort)
                val str2 = index (sort_to_string sort)

                val oper_aequiv =
                    if #mutualwith ana abt_or_sort (Sort sort)
                    then
                      SeqExp
                        [ExpVar "Abt.aequiv",
                         ExpVar (sort_to_string sort ^ "_oper_aequiv")]
                    else ExpVar (Big (sort_to_string sort) ^ ".aequiv")
              in
                (VarPat str1,
                 VarPat str2,
                 SeqExp
                   [oper_aequiv,
                    TupleExp [ExpVar str1, ExpVar str2]])
              end,
           sym_bindingf =
           fn sym => (Wild, Wild, ExpVar "true"),
           sort_bindingf =
           fn sort => (Wild, Wild, ExpVar "true"),
           prodf =
           fn patexps =>
              let
                val (pats1, pats2, exps) =
                    unzip3 patexps
              in
                (TuplePat pats1,
                 TuplePat pats2,
                 SeqExp (interleave BoolAnd exps))
              end,
           listf =
           fn (pat1, pat2, exp) =>
              let
                val str1 = index "list"
                val str2 = index "list"
              in
                (VarPat str1,
                 VarPat str2,
                 SeqExp
                   [ExpVar "ListPair.all",
                    LamExp [(TuplePat [pat1, pat2], exp)],
                    TupleExp [ExpVar str1, ExpVar str2]])
              end,
           extf =
           fn (ext, patexps) =>
              let
                val str1 = index (ext_to_string ext)
                val str2 = index (ext_to_string ext)
              in
                (VarPat str1,
                 VarPat str2,
                 SeqExp
                   (ExpVar (Big (ext_to_string ext) ^ ".equal")
                    :: List.map
                         (fn (pat1, pat2, exp) =>
                             LamExp [(TuplePat [pat1, pat2], exp)])
                         patexps
                    @ [TupleExp [ExpVar str1, ExpVar str2]]))
              end,
           abtf =
           fn (abt, patexps) =>
              let
                val str1 = index (abt_to_string abt)
                val str2 = index (abt_to_string abt)
                val aequiv_str =
                    if internal_abt
                    then "internal_aequiv"
                    else "aequiv"
              in
                (VarPat str1,
                 VarPat str2,
                 if #mutualwith ana abt_or_sort (Abt abt)
                 then
                   SeqExp
                     [ExpVar (abt_to_string abt ^ "_" ^ aequiv_str),
                      TupleExp [ExpVar str1, ExpVar str2]]
                 else
                   SeqExp
                     [ExpVar (Big (abt_to_string abt) ^ "." ^ aequiv_str),
                      TupleExp [ExpVar str1, ExpVar str2]])
              end,
           dotf =
           fn ((patl1, patr1, exp1), (patl2, patr2, exp2)) =>
              (TuplePat [patl1, patl2],
               TuplePat [patr1, patr2],
               SeqExp [exp1, BoolAnd, exp2])}
      end

  fun paramf str = str ^ "_aequiv"
in
fun abt_aequiv ana internal (abt, (args, opers)) =
    (abt_to_string abt ^
     (if internal
      then "_internal_aequiv"
      else "_aequiv"),
     List.map (VarPat o paramf) args
     @ [TuplePat
          [VarPat (abt_to_string abt ^ "1"),
           VarPat (abt_to_string abt ^ "2")]],
     NONE,
     CaseExp
       (TupleExp
          [ExpVar (abt_to_string abt ^ "1"),
           ExpVar (abt_to_string abt ^ "2")],
        List.map
          (fn (oper, arity_opt) =>
              let
                val oper' =
                    if internal
                    then internal_oper (Abt abt) oper
                    else oper
              in
                case arity_opt of
                    NONE =>
                    (TuplePat [VarPat oper', VarPat oper'],
                     ExpVar "true")
                  | SOME arity =>
                    let
                      val (pat1, pat2, exp) =
                          #1 (aequiv_code ana (Abt abt) internal)
                             (fn str =>
                                 (VarPat (str ^ "1"),
                                  VarPat (str ^ "2"),
                                  SeqExp
                                    [ExpVar (paramf str),
                                     TupleExp
                                       [ExpVar (str ^ "1"),
                                        ExpVar (str ^ "2")]]))
                             arity
                    in
                      (TuplePat
                         [InjPat (oper', pat1),
                          InjPat (oper', pat2)],
                       exp)
                    end
              end)
          opers
        @ [(Wild, ExpVar "false")]))

fun sort_aequiv ana (sort, opers) =
    (sort_to_string sort ^ "_oper_aequiv",
     [TuplePat
        [VarPat (sort_to_string sort ^ "1"),
         VarPat (sort_to_string sort ^ "2")]],
     NONE,
     CaseExp
       (TupleExp
          [ExpVar (sort_to_string sort ^ "1"),
           ExpVar (sort_to_string sort ^ "2")],
        List.map
          (fn (oper, arity_opt) =>
              case arity_opt of
                  NONE =>
                  (TuplePat
                     [VarPat (internal_oper (Sort sort) oper),
                      VarPat (internal_oper (Sort sort) oper)],
                   ExpVar "true")
                | SOME arity =>
                  let
                    val (pat1, pat2, exp) =
                        #2 (aequiv_code ana (Sort sort) true) arity
                  in
                    (TuplePat
                       [InjPat (internal_oper (Sort sort) oper, pat1),
                        InjPat (internal_oper (Sort sort) oper, pat2)],
                     exp)
                  end)
          opers
        @ [(Wild, ExpVar "false")]))
end


fun create_mutual_ops (ana : ana) (abts, sorts) =
    let
(*??? should actually use this or similar.
      fun scoped_sort srt srt' =
          if #mutualwith ana srt srt'
          then sort_to_string srt'
          else ops_name ana srt' ^ "." ^ sort_to_string srt'
*)

      val abt_datatypes =
          List.map
            (fn (abt, (args, opers)) =>
                (abt_to_string abt,
                 List.map (fn arg => "'" ^ arg) args,
                 List.map
                   (fn (oper, arity_opt) =>
                       (Big (abt_to_string abt) ^ "'" ^ oper,
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
                       (Big (sort_to_string sort) ^ "'" ^ oper,
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
                    ModProjType (StructVar "Abt", "t"))))
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

        fun sym_bindingf (sym, exp) = exp

        fun sort_bindingf (sort, exp) = exp

        val prodf = TupleExp

        fun extf (ext, exp, patexps) =
            case patexps of
                [] => exp
              | _ =>
                SeqExp
                  [LamExp [(TuplePat [VarPat "x", Wild], ExpVar "x")],
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

        fun oper_patf abt_or_sort (oper, pat_opt) =
            case pat_opt of
                NONE =>
                VarPat (internal_oper abt_or_sort oper)
              | SOME pat =>
                InjPat
                  (internal_oper abt_or_sort oper, pat)

        fun operf abt_or_sort (oper, exp_opt) =
            case exp_opt of
                NONE =>
                ExpVar (internal_oper abt_or_sort oper)
              | SOME exp =>
                SeqExp
                  [ExpVar
                     (internal_oper abt_or_sort oper),
                   exp]

        fun ident l = l (* make this more global ??? *)

        fun recs name abt_or_sort =
            create_recursors
              {name =
               case abt_or_sort of
                   Abt abt => abt_to_string abt ^ "_" ^ name
                 | Sort sort => sort_to_string sort ^ "_oper_" ^ name,
               args = args,
               sym_usef = sym_usef name,
               sort_usef = sort_usef name abt_or_sort,
               sym_bindingf = sym_bindingf,
               sort_bindingf = sort_bindingf,
               prodf = TupleExp,
               listf = ident,
               extf = extf,
               abtf = abtf name abt_or_sort,
               dotf =
               fn (binding_exp, arity_exp) =>
                  TupleExp [binding_exp, arity_exp],
               oper_patf = oper_patf abt_or_sort,
               operf = operf abt_or_sort}
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
                @ List.map (sort_rec "unbind") sorts),
             BlankDefn,
             FunDefns
               (List.map (abt_aequiv ana true) abts
                @ List.map (sort_aequiv ana) sorts)]))
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
          then ("Var", SOME (TypeVar (sort_to_var_type srt))) :: oper_branches
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
                 (InjPat ("Abt.Binding", TuplePat [Wild, VarPat "acc'"]),
                  SeqExp
                    [ExpVar "Abt.out",
                     oper_unbind,
                     SeqExp
                       [ExpVar "Abt.unbind",
                        oper_unbind,
                        ExpVar "x",
                        IntExp ~1, (* This violates every invariant... *)
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
          LetExp
            ([ValDefn (VarPat "var", exp)],
             TupleExp
               [SeqExp [ExpVar "Temp.toUserString", ExpVar "var"],
                ListExp [ExpVar "var"]]),

       sort_bindingf =
       fn (sort, exp) =>
          LetExp
            ([ValDefn (VarPat "var", exp)],
             TupleExp
               [SeqExp [ExpVar "Temp.toUserString", ExpVar "var"],
                ListExp [ExpVar "var"]]),

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
                         ^ Big (abt_to_string abt) ^ "'" ^ oper),
                      ListExp []]
                 | SOME exp =>
                   LetExp
                     ([ValDefn (TuplePat [VarPat "t", VarPat "vars'"], exp)],
                      TupleExp
                        [SeqExp
                           [ExpVar
                              (ops_name ana (Abt abt) ^ "."
                               ^ Big (abt_to_string abt) ^ "'" ^ oper),
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
                         ^ Big (sort_to_string sort) ^ "'" ^ oper)]
                 | SOME exp =>
                   SeqExp
                     [ExpVar "Abt.Oper",
                      SeqExp
                        [ExpVar
                           (ops_name ana (Sort sort) ^ "."
                            ^ Big (sort_to_string sort) ^ "'" ^ oper),
                         SeqExp
                           [LamExp [(TuplePat [VarPat "x", Wild], ExpVar "x")],
                            exp]]])}

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
            ([ValDefn (VarPat "x", SeqExp [ExpVar "Temp.new", exp])],
             TupleExp [ExpVar "x", ListExp [ExpVar "x"]]),

       sort_bindingf =
       fn (sort, exp) =>
          LetExp
            ([ValDefn (VarPat "x", SeqExp [ExpVar "Temp.new", exp])],
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
                 ^ Big (abt_or_sort_to_string abt_or_sort) ^ "'" ^ oper)
            | SOME pat =>
              InjPat
                (ops_name ana abt_or_sort ^ "."
                 ^ Big (abt_or_sort_to_string abt_or_sort) ^ "'" ^ oper,
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
                   SeqExp
                     [ExpVar oper,
                      SeqExp
                        [LamExp [(TuplePat [VarPat "x", Wild], ExpVar "x")],
                         exp]])}

fun create_mutual_abt_view_datatype ana abts =
    case abts of
        [] => []
      | (abt, _)::_ =>
        interleave BlankDefn
          (List.map TypeDefns (#2 (create_mutual_types ana (Abt abt)))
           @ [TypeDefns
                {datatypes=List.map (abt_datatype ana) abts,
                 aliases=[]},
              FunDefns
                (List.map
                   (fn (abt, (args, opers)) =>
                       #1 (view_in_code ana (Abt abt)) (abt, args, opers))
                   abts),
              FunDefns
                (List.map
                   (fn (abt, (args, opers)) =>
                       #1 (view_out_code ana (Abt abt)) (abt, args, opers))
                   abts)])

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
              FunDefns
                [(name, args, typ,
                  CaseExp
                    (exp,
                     (InjPat ("Var", VarPat "x"),
                      SeqExp [ExpVar "Abt.Var", ExpVar "x"])
                     :: cases))]
            else FunDefns [(name, args, typ, CaseExp (exp, cases))]
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

      val all_defns =
          List.concat
            [List.map TypeDefns (op@ (create_mutual_types ana (Sort sort))),
             [TypeDefns
                {datatypes = [],
                 aliases =
                 [(sort_to_string sort,
                   [],
                   ModProjType
                     (StructVar (ops_name ana (Sort sort)),
                      sort_to_string sort))]},
              TypeDefns
                {datatypes = [],
                 aliases = [("t", [], sort_to_type sort)]},
              BlankDefn],
             var_structure_defn,
             [BlankDefn,
              create_view_datatype_defn ana (sort, opers),
              BlankDefn,
              view_in_code,
              BlankDefn,
              FunDefns [oper_view_out_code],
              BlankDefn,
              view_out_code,
              BlankDefn,
              into_code,
              out_code,
              BlankDefn],
             convenient_contructors]
    in
      StructureDefn (Big (sort_to_string sort), NONE, StructBody all_defns)
    end

fun create_mutual_utils (ana : ana) (abts, sorts) =
    let
      fun toString_code abt_or_sort =
          create_recursors
            {name = abt_or_sort_to_string abt_or_sort ^ "_toString",
             args = [],
             sym_usef =
             fn (sym, exp) =>
                SeqExp [ExpVar (Big (sym_to_string sym) ^ ".toString"), exp],
             sort_usef =
             fn (sort, exp) =>
                if #mutualwith ana abt_or_sort (Sort sort)
                then SeqExp [ExpVar (sort_to_string sort ^ "_toString"), exp]
                else SeqExp [ExpVar (Big (sort_to_string sort) ^ ".toString"), exp],
             sym_bindingf =
             fn (sym, exp) =>
                SeqExp [ExpVar (Big (sym_to_string sym) ^ ".toString"), exp],
             sort_bindingf =
             fn (sort, exp) =>
                SeqExp [ExpVar (Big (sort_to_string sort) ^ ".Var.toString"), exp],
             prodf =
             fn exps =>
                SeqExp
                  ([StringExp "(", ExpVar "^"]
                   @ concatWith
                       [ExpVar "^", StringExp ", ", ExpVar "^"]
                       (List.map (fn exp => [exp]) exps)
                   @ [ExpVar "^", StringExp ")"]),
             listf =
             fn exp =>
                SeqExp
                  [StringExp "[",
                   ExpVar "^",
                   ExpVar "String.concatWith",
                   StringExp ", ",
                   exp,
                   ExpVar "^",
                   StringExp "]"],
             extf =
             fn (ext, exp, patexps) =>
                SeqExp
                  (ExpVar (Big (ext_to_string ext) ^ ".toString")
                   :: List.map (fn patexp => LamExp [patexp]) patexps
                   @ [exp]),
             abtf =
             fn abt =>
                if #mutualwith ana abt_or_sort (Abt abt)
                then ExpVar (abt_to_string abt ^ "_toString")
                else ExpVar (Big (abt_to_string abt) ^ ".toString"),
             dotf =
             fn (exp1, exp2) =>
                SeqExp
                  [StringExp "(",
                   ExpVar "^",
                   exp1,
                   ExpVar "^",
                   StringExp " . ",
                   ExpVar "^",
                   exp2,
                   ExpVar "^",
                   StringExp ")"],
             oper_patf =
             fn (oper, pat_opt) =>
                case pat_opt of
                    NONE =>
                    VarPat (Big (abt_or_sort_to_string abt_or_sort) ^ "." ^ oper)
                  | SOME pat =>
                    InjPat (Big (abt_or_sort_to_string abt_or_sort) ^ "." ^ oper, pat),
             operf =
             fn (oper, exp_opt) =>
                case exp_opt of
                    NONE => StringExp oper
                  | SOME exp =>
                    SeqExp
                      [StringExp ("(" ^ oper ^ " "),
                       ExpVar "^",
                       exp,
                       ExpVar "^",
                       StringExp ")"]}

      val abt_toStrings =
          List.map
            (fn (abt, (args, opers)) =>
                #1 (toString_code (Abt abt)) (abt, args, opers))
            abts

      val sort_toStrings =
          List.map
            (fn (sort, opers) =>
                let
                  val (name, args, typ, CaseExp (exp, cases)) = (* This is ugly ??? *)
                      #2 (toString_code (Sort sort)) (sort, opers)
                in
                  (name, args, typ,
                   CaseExp
                     (SeqExp [ExpVar (Big (sort_to_string sort) ^ ".out"), exp],
                      if #hasvar ana sort
                      then
                        (InjPat
                           (Big (sort_to_string sort) ^ ".Var", VarPat "x"),
                         SeqExp
                           [ExpVar
                              (Big (sort_to_string sort) ^ ".Var.toString"),
                            ExpVar "x"])
                        :: cases
                      else cases))
                end)
            sorts

      fun subst_code abt_or_sort sort =
          let
            fun name abt_or_sort' =
                (if #mutualwith ana abt_or_sort abt_or_sort'
                 then abt_or_sort_to_string abt_or_sort' ^ "_"
                 else Big (abt_or_sort_to_string abt_or_sort') ^ ".")
                ^ "subst"
                ^ (if abt_or_sort' = Sort sort
                   then ""
                   else Big (sort_to_string sort))
          in
            create_recursors
              {name = name abt_or_sort,
               args = ["t", "x"],
               sym_usef =
               fn (sym, exp) => exp,
               sort_usef =
               fn (sort', exp) =>
                  if #dependson ana (Sort sort') (Sort sort)
                  then SeqExp [ExpVar (name (Sort sort')), ExpVar "t", ExpVar "x", exp]
                  else exp,
               sym_bindingf =
               fn (sym, exp) => exp,
               sort_bindingf =
               fn (sort, exp) => exp,
               prodf = TupleExp,
               listf = fn l => l,
               extf =
               fn (ext, exp, patexps) =>
                  (case patexps of
                    [] => exp
                  | _ =>
                    SeqExp
                      (ExpVar (Big (ext_to_string ext) ^ ".map")
                       :: List.map (fn patexp => LamExp [patexp]) patexps
                       @ [exp])),
               abtf =
               fn abt =>
                  if #dependson ana (Abt abt) (Sort sort)
                  then ExpVar (name (Abt abt))
                  else LamExp [(Wild, LamExp [(Wild, LamExp [(VarPat "t", ExpVar "t")])])],
               dotf =
               fn (exp1, exp2) =>
                  TupleExp [exp1, exp2],
               oper_patf =
               fn (oper, pat_opt) =>
                  case pat_opt of
                      NONE =>
                      VarPat (Big (abt_or_sort_to_string abt_or_sort) ^ "." ^ oper)
                    | SOME pat =>
                      InjPat (Big (abt_or_sort_to_string abt_or_sort) ^ "." ^ oper, pat),
               operf =
               fn (oper, exp_opt) =>
                  case exp_opt of
                      NONE =>
                      ExpVar
                        (Big (abt_or_sort_to_string abt_or_sort)
                         ^ "." ^ oper
                         ^ (case abt_or_sort of Abt _ => "" | Sort _ => "'"))
                    | SOME exp =>
                      SeqExp
                        [ExpVar
                           (Big (abt_or_sort_to_string abt_or_sort)
                            ^ "." ^ oper
                            ^ (case abt_or_sort of Abt _ => "" | Sort _ => "'")),
                         exp]}
          end

      val substitutions =
          List.concat
            (List.map
               (fn (abt, (args, opers)) =>
                   List.map
                     (fn sort' =>
                         #1 (subst_code (Abt abt) sort') (abt, args, opers))
                     (List.filter
                        (#hasvar ana)
                        (#2 (#dependencies ana (Abt abt)))))
               abts)
          @ List.concat
              (List.map
                 (fn (sort, opers) =>
                     List.map
                       (fn sort' =>
                           let
                             val (name, args, typ_opt, CaseExp (exp, cases)) =
                                 #2 (subst_code (Sort sort) sort') (sort, opers)
                           in
                             (name, args, typ_opt,
                              CaseExp
                                (SeqExp
                                   [ExpVar (Big (sort_to_string sort) ^ ".out"),
                                    exp],
                                 if #hasvar ana sort
                                 then
                                   if sort = sort'
                                   then
                                     (InjPat (Big (sort_to_string sort) ^ ".Var", VarPat "y"),
                                      IfExp
                                        (SeqExp
                                           [ExpVar (Big (sort_to_string sort) ^ ".Var.equal"),
                                            TupleExp [ExpVar "x", ExpVar "y"]],
                                         ExpVar "t",
                                         SeqExp
                                           [ExpVar (Big (sort_to_string sort) ^ ".Var'"),
                                            ExpVar "y"]))
                                     :: cases
                                   else
                                     (InjPat (Big (sort_to_string sort) ^ ".Var", VarPat "y"),
                                   SeqExp
                                     [ExpVar (Big (sort_to_string sort) ^ ".Var'"),
                                      ExpVar "y"])
                                     :: cases
                                 else cases))
                           end)
                       (List.filter
                          (#hasvar ana)
                          (#2 (#dependencies ana (Sort sort)))))
                 sorts)
    in
      [FunDefns (List.map (abt_aequiv ana false) abts),
       FunDefns (abt_toStrings @ sort_toStrings),
       FunDefns substitutions]
    end

fun create_structure_with_utils ana (abt_or_sort, deps) =
    let val name = abt_or_sort_to_string abt_or_sort in
      StructureDefn
        (Big name,
         NONE,
         StructBody
           (OpenDefn (StructVar (Big name))
            :: ValDefn (VarPat "toString", ExpVar (name ^ "_toString"))
            :: (case abt_or_sort of
                 Abt abt =>
                 [ValDefn
                    (VarPat "internal_aequiv",
                     ExpVar
                       (ops_name ana abt_or_sort ^ "." ^ name ^ "_internal_aequiv")),
                  ValDefn
                    (VarPat "aequiv",
                     ExpVar
                       (name ^ "_aequiv"))]
               | Sort _ =>
                 [ValDefn
                    (VarPat "aequiv",
                     SeqExp
                       [ExpVar "Abt.aequiv",
                        ExpVar
                          (ops_name ana abt_or_sort ^ "." ^ name ^ "_oper_aequiv")])])
            @ List.map
                (fn sort' =>
                    let
                      val subst_name =
                          if abt_or_sort = Sort sort'
                          then "subst"
                          else "subst" ^ Big (sort_to_string sort')
                    in
                      ValDefn
                        (VarPat subst_name, ExpVar (name ^ "_" ^ subst_name))
                    end)
                deps))
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
                     @ create_mutual_utils ana (abts, sorts)
                     @ List.map
                         (create_structure_with_utils ana)
                         (List.map
                            (fn (abt, _) =>
                                (Abt abt,
                                 List.filter
                                   (#hasvar ana)
                                   (#2 (#dependencies ana (Abt abt)))))
                            abts
                          @ List.map
                              (fn (sort, _) =>
                                  (Sort sort,
                                   List.filter
                                     (#hasvar ana)
                                     (#2 (#dependencies ana (Sort sort)))))
                              sorts)
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
                      ModProjType (StructVar (Big (ext_to_string ext)), "t")),
                   AppType
                     (List.map (fn arg => TypeVar ("'" ^ arg)) args,
                      ModProjType (StructVar (Big (ext_to_string ext)), "t"))))
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
