(* Core functionality about the way abbot maps sorts to SML types *)

structure AbbotCore =
struct

open Util
infixr 0 >>
open Analysis
open SmlSyntax

fun Big s =
    Char.toString (Char.toUpper (String.sub (s, 0)))
    ^ String.extract (s, 1, NONE)

fun BIG s = String.map Char.toUpper s

fun sort_to_type s =
    TypeVar (sort_to_string s)

fun sort_to_var_type s =
    sort_to_string s ^ "Var"

fun sym_to_type s =
    TypeVar (sym_to_string s)

fun ops_name (ana : ana) srt =
    let val (mut_abts, mut_sorts) = #mutual ana srt in
      String.concat
        (List.map (Big o abt_to_string) mut_abts
         @ List.map (Big o sort_to_string) mut_sorts)
      ^ "Ops"
    end

fun create_abt_and_sort_fun
      {sym_usef : symbol -> 'a,
       sort_usef : sort -> 'a,
       sym_bindingf : symbol -> 'a,
       sort_bindingf : sort -> 'a,
       prodf : 'a list -> 'a,
       listf : 'a -> 'a,
       extf : ext * 'a list -> 'a,
       abtf : abt * 'a list -> 'a,
       dotf : 'a * 'a -> 'a}
    : ((string -> 'a) -> AbtArity.t -> 'a) * (SortArity.t -> 'a) =
    (fn paramf =>
        let
          open AbtArity
          fun abt_fun arity =
              case arity of
                  Param str => paramf str
                | SymbolUse sym => sym_usef sym
                | SortUse sort => sort_usef sort
                | SymbolBinding sym => sym_bindingf sym
                | SortBinding sort => sort_bindingf sort
                | Prod aritys => prodf (List.map abt_fun aritys)
                | List arity => listf (abt_fun arity)
                | AppExt (ext, aritys) =>
                  extf (ext, List.map abt_fun aritys)
                | AppAbt (abt, aritys) =>
                  abtf (abt, List.map abt_fun aritys)
                | Dot (binding, arity) =>
                  dotf (abt_fun binding, abt_fun arity)
        in
          abt_fun
        end,
     let
       open SortArity
       fun sort_fun arity =
           case arity of
               SymbolUse sym => sym_usef sym
             | SortUse sort => sort_usef sort
             | SymbolBinding sym => sym_bindingf sym
             | SortBinding sort => sort_bindingf sort
             | Prod aritys => prodf (List.map sort_fun aritys)
             | List arity => listf (sort_fun arity)
             | AppExt (ext, aritys) =>
               extf (ext, List.map sort_fun aritys)
             | AppAbt (abt, aritys) =>
               abtf (abt, List.map sort_fun aritys)
             | Dot (binding, arity) =>
               dotf (sort_fun binding, sort_fun arity)
    in
      sort_fun
    end)

fun arity_to_type (ana : ana) internal abt_or_sort =
    create_abt_and_sort_fun
      {sym_usef =
       fn sym =>
          if internal
          then
            AppType
              ([TypeVar "unit"],
               ModProjType (StructVar "Abt", "t"))
          else ModProjType (StructVar (Big (sym_to_string sym)), "t"),
       sort_usef =
       fn srt =>
          if #mutualwith ana abt_or_sort (Sort srt)
          then sort_to_type srt
          else ModProjType (StructVar (Big (sort_to_string srt)), "t"),
       sym_bindingf =
       fn sym =>
          if internal
          then TypeVar "string"
          else ModProjType (StructVar (Big (sym_to_string sym)), "t"),
       sort_bindingf =
       fn srt =>
          if internal
          then TypeVar "string"
          else if #mutualwith ana abt_or_sort (Sort srt)
          then TypeVar (sort_to_var_type srt)
          else
            ModProjType
              (StructVar (Big (sort_to_string srt)),
               sort_to_var_type srt),
       prodf = ProdType,
       listf = fn typ => AppType ([typ], TypeVar "list"),
       extf =
       fn (ext, typs) =>
          AppType
            (typs, ModProjType (StructVar (Big (ext_to_string ext)), "t")),
       abtf =
       fn (abt, typs) =>
          AppType
            (typs,
             if #mutualwith ana abt_or_sort (Abt abt)
             then TypeVar (abt_to_string abt)
             else if internal
             then
               ModProjType
                 (StructVar (ops_name ana (Abt abt)),
                  abt_to_string abt)
             else
               ModProjType (StructVar (Big (abt_to_string abt)), "t")),
       dotf =
       fn (binding_typ, arity_typ) =>
          ProdType [binding_typ, arity_typ]}

fun abt_arity_to_type (ana : ana) internal abt =
    #1 (arity_to_type ana internal (Abt abt)) (fn str => TypeVar ("'" ^ str))

fun sort_arity_to_type (ana : ana) internal sort =
    #2 (arity_to_type ana internal (Sort sort))

fun create_ext_signature args =
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
                         ArrowType
                           (ArrowType
                              (ProdType [TypeVar ("'" ^ arg ^ "1"),
                                         TypeVar "'state"],
                               ProdType [TypeVar ("'" ^ arg ^ "2"),
                                         TypeVar "'state"]),
                            acc))
                     (ArrowType
                        (ProdType
                           [AppType
                              (List.map
                                 (fn arg => TypeVar ("'" ^ arg ^ "1"))
                                 args,
                               TypeVar "t"),
                            TypeVar "'state"],
                         ProdType
                           [AppType
                              (List.map
                                 (fn arg => TypeVar ("'" ^ arg ^ "2"))
                                 args,
                               TypeVar "t"),
                            TypeVar "'state"]))
                     args)]))

fun abt_datatype ana (abt, (args, opers)) =
    (abt_to_string abt,
     List.map (fn arg => "'" ^ arg) args,
     List.map
       (fn (oper, arity_opt) =>
           (oper,
            case arity_opt of
                NONE => NONE
              | SOME arity => SOME (abt_arity_to_type ana false abt arity)))
       opers)

fun create_mutual_types (ana : ana) abt_or_sort =
    let
      val (mut_abts, mut_sorts) = #mutual ana abt_or_sort

      val (other_abts, other_sorts) =
          case abt_or_sort of
              Abt abt =>
              (List.filter (fn abt' => abt' <> abt) mut_abts, mut_sorts)
            | Sort sort =>
              (mut_abts, List.filter (fn sort' => sort' <> sort) mut_sorts)

      val mutual_abt_types =
          List.map
            (fn abt =>
                {datatypes = [],
                 aliases =
                 [(abt_to_string abt,
                   [(* ??? #args ana abt *)],
                   TypeVar (abt_to_string abt))]})
            other_abts

      val mutual_sort_types =
          List.map
            (fn sort =>
                {datatypes = [],
                 aliases =
                 [(sort_to_string sort,
                   [],
                   ModProjType
                     (StructVar (ops_name ana (Sort sort)),
                      sort_to_string sort))]})
            other_sorts

      val mutual_var_types =
          List.map
            (fn var_srt =>
                {datatypes = [],
                 aliases =
                 [(sort_to_string var_srt ^ "Var",
                   [],
                   ModProjType (StructVar "Temp", "t"))]})
            (List.filter (#hasvar ana) mut_sorts)
    in
      (mutual_abt_types, mutual_sort_types @ mutual_var_types)
    end
end
