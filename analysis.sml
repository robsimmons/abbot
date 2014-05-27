functor MkAnalyis
          (val parse_data : Syntax.oper list StringTable.table * string list)
        : ANALYSIS =
struct
  open Syntax

  val (sorts, symbs) = parse_data

  fun issrt s =
      case StringTable.find sorts s of
          NONE => false
        | SOME _ => true

  fun issym s =
      List.exists (fn a => a = s) symbs

  val binding_table =
      StringTable.map
        (fn opers =>
            List.foldl
              StringTable.Set.union
              (StringTable.Set.empty ())
              (List.map
                 (fn {name, arity} =>
                     List.foldl
                       StringTable.Set.union
                       (StringTable.Set.empty ())
                       (List.map
                          (StringTable.Set.fromSeq
                           o StringTable.Seq.fromList
                           o #1)
                          arity))
                 opers))
        sorts

  fun binds s1 s2 =
      case StringTable.find binding_table s1 of
          NONE => false
        | SOME bound => StringTable.Set.find bound s2

  val set_to_list = StringTable.Seq.toList o StringTable.Set.toSeq

  val varsym_table =
      StringTable.map
        (fn opers =>
            List.foldl
              StringTable.Set.union
              (StringTable.Set.empty ())
              (List.map
                 (fn {name, arity} =>
                     List.foldl
                       StringTable.Set.union
                       (StringTable.Set.empty ())
                       (List.map
                          (StringTable.Set.singleton o #2)
                          arity))
                 opers))
        sorts

  val var_table = StringTable.map (StringTable.Set.filter issrt) varsym_table
  val varin = set_to_list o valOf o StringTable.find var_table

  val sym_table = StringTable.map (StringTable.Set.filter issym) varsym_table
  val symin = set_to_list o valOf o StringTable.find sym_table

  (* Should this also consider bindings???
   * Also, this is broken for cycles of mutual sorts with length > 2 *)
  val mutual_table =
      StringTable.mapk
        (fn (s, varsin) =>
            StringTable.Set.filter
              (fn s' =>
                  case StringTable.find var_table s' of
                      NONE => false
                    | SOME varsin' =>
                      StringTable.Set.find varsin' s)
              varsin)
        var_table

  fun mutual' s =
      StringTable.find mutual_table s

  val mutual = set_to_list o valOf o mutual'

  fun mutualwith s1 s2 =
      case mutual' s1 of
          NONE => false
        | SOME mutuals => StringTable.Set.find mutuals s2
end
