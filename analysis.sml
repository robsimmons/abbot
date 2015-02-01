structure Analysis :> sig
  eqtype ext

  val ext_to_string : ext -> string

  eqtype symbol

  val sym_to_string : symbol -> string

  eqtype abt

  val abt_to_string : abt -> string

  eqtype sort

  val sort_to_string : sort -> string

  structure AbtArity : sig
    datatype t
      = Param of string (* paramaterized arity *)
      | SymbolUse of symbol (* symbol use *)
      | SortUse of sort (* sort use *)
      | SymbolBinding of symbol (* symbol binding *)
      | SortBinding of sort (* sort binding *)
      | Prod of t list
      | List of t
      | AppExt of ext * t list
      | AppAbt of abt * t list
      | Dot of t * t (* Binds bindings on the left in the right. *)
  end

  structure SortArity : sig
    datatype t
      = SymbolUse of symbol (* symbol use *)
      | SortUse of sort (* sort use *)
      | SymbolBinding of symbol (* symbol binding *)
      | SortBinding of sort (* sort binding *)
      | Prod of t list
      | List of t
      | AppExt of ext * t list
      | AppAbt of abt * t list
      | Dot of t * t (* Binds bindings on the left in the right. *)
  end

  datatype abt_or_sort = Abt of abt | Sort of sort

  val abt_or_sort_to_string : abt_or_sort -> string

  type ana = {
    (* External abts and their arguements. *)
    externals : (ext * string list) list,

    (* All symbols. *)
    symbols : symbol list,

    (* All internal abts and sorts and their associated operations and aritys.
     * They are grouped with their mutual dependencies and occur
     * later in the outer list than their strict dependencies. *)
    abts_and_sorts
    : (abt * (string list * (string * AbtArity.t option) list),
       sort * (string * SortArity.t option) list) Util.Sum2.t list list,

    (* Whether the list abt structure needs to be included. *)
    haslist : bool,

    (* Argument strings for the given abt. *)
    args : abt -> string list,

    (* Whether the given sort can be bound to a variable. *)
    hasvar : sort -> bool,

    (* Abts and sorts that the given abt or sort refers to. *)
    dependencies : abt_or_sort -> abt list * sort list,

    (* Returns true iff the first abt or sort given depends on the second. *)
    dependson : abt_or_sort -> abt_or_sort -> bool,

    (* Returns all the mutually dependent abts and sorts
     * of a given abt or sort, including itself. *)
    mutual : abt_or_sort -> abt list * sort list,

    (* Returns true iff the given abts or sorts are mutually dependent. *)
    mutualwith : abt_or_sort -> abt_or_sort -> bool
  }

  val analyze : string list StringTable.table
                * StringTable.Set.set
                * (string list * AbbotSyntax.oper list) StringTable.table
                * AbbotSyntax.oper list StringTable.table
                -> ana
end = struct
  open Util
  open StringTable

  type ext = string

  fun ext_to_string x = x

  type symbol = string

  fun sym_to_string x = x

  type abt = string

  fun abt_to_string x = x

  type sort = string

  fun sort_to_string x = x

  structure AbtArity = struct
    datatype t
      = Param of string (* paramaterized arity *)
      | SymbolUse of symbol (* symbol use *)
      | SortUse of sort (* sort use *)
      | SymbolBinding of symbol (* symbol binding *)
      | SortBinding of symbol (* sort binding *)
      | Prod of t list
      | List of t
      | AppExt of ext * t list
      | AppAbt of abt * t list
      | Dot of t * t (* Binds bindings on the left in the right. *)
  end

  structure SortArity = struct
    datatype t
      = SymbolUse of symbol (* symbol use *)
      | SortUse of sort (* sort use *)
      | SymbolBinding of symbol (* symbol binding *)
      | SortBinding of symbol (* sort binding *)
      | Prod of t list
      | List of t
      | AppExt of ext * t list
      | AppAbt of abt * t list
      | Dot of t * t (* Binds bindings on the left in the right. *)
  end

  datatype abt_or_sort = Abt of abt | Sort of sort

  fun abt_or_sort_to_string (Abt s | Sort s) = s

  type ana = {
    externals : (ext * string list) list,
    symbols : symbol list,
    abts_and_sorts
    : (abt * (string list * (string * AbtArity.t option) list),
       sort * (string * SortArity.t option) list) Util.Sum2.t list list,
    haslist : bool,
    args : abt -> string list,
    hasvar : sort -> bool,
    dependencies : abt_or_sort -> abt list * sort list,
    dependson : abt_or_sort -> abt_or_sort -> bool,
    mutual : abt_or_sort -> abt list * sort list,
    mutualwith : abt_or_sort -> abt_or_sort -> bool
  }

  local open AbtArity in
  fun convert_abt_arity (exts, symbs, abts, sorts) arity =
      case arity of
          AbbotSyntax.Param name => Param name
        | AbbotSyntax.Use name =>
          (if Set.find sorts name
           then SortUse name
           else if Set.find symbs name
           then SymbolUse name
           else if Set.find abts name
           then AppAbt (name, [])
           else if Set.find exts name
           then AppExt (name, [])
           else raise Fail (name ^ " is not a defined symbol, abt, or sort.")) (*???location*)
        | AbbotSyntax.Binding name =>
          (if Set.find sorts name
           then SortBinding name
           else if Set.find symbs name
           then SymbolBinding name
           else raise Fail (name ^ " is not a sort or symbol, so it cannot be bound.")) (*???location*)
        | AbbotSyntax.Prod aritys =>
          Prod (List.map (convert_abt_arity (exts, symbs, abts, sorts)) aritys)
        | AbbotSyntax.App ("list", [arity]) =>
          List (convert_abt_arity (exts, symbs, abts, sorts) arity)
        | AbbotSyntax.App (name, aritys) =>
          (if Set.find abts name
           then
             AppAbt
               (name,
                List.map
                  (convert_abt_arity (exts, symbs, abts, sorts))
                  aritys)
           else if Set.find exts name
           then
             AppExt
               (name,
                List.map
                  (convert_abt_arity (exts, symbs, abts, sorts))
                  aritys)
           else raise Fail (name ^ " is not a defined abt.")) (*???location*)
        | AbbotSyntax.Dot (binding, arity) =>
          Dot
            (convert_abt_arity (exts, symbs, abts, sorts) binding,
             convert_abt_arity (exts, symbs, abts, sorts) arity)

  val depth = ref 0

  fun abt_arity_binds abt abts arity =
      case arity of
          (Param _ | SymbolUse _ | SortUse _) => false
        | (SymbolBinding _ | SortBinding _) => true
        | List arity => abt_arity_binds abt abts arity
        | (Prod aritys | AppExt (_, aritys)) =>
          List.exists (abt_arity_binds abt abts) aritys
        | AppAbt (abt', aritys) =>
          List.exists (abt_arity_binds abt abts) aritys
          orelse
          if abt = abt' then false else (* ???This will diverge under mutual dependence *)
          let val (args, opers) = valOf (find abts abt') in
            List.exists
              (fn (_, arity_opt) =>
                  case arity_opt of
                      NONE => false
                    | SOME arity => abt_arity_binds abt' abts arity)
              opers
          end
        | Dot (_, arity) => abt_arity_binds abt abts arity
  end

  local open SortArity in
  fun convert_sort_arity (exts, symbs, abts, sorts) arity =
      case arity of
          AbbotSyntax.Param _ =>
          raise Fail "Sorts may not have parameters." (*???location, also this might be a bad error message*)
        | AbbotSyntax.Use name =>
          (if Set.find sorts name
           then SortUse name
           else if Set.find symbs name
           then SymbolUse name
           else if Set.find exts name
           then AppExt (name, [])
           else if Set.find abts name
           then AppAbt (name, [])
           else raise Fail (name ^ " is not a defined symbol, abt, or sort.")) (*???location*)
        | AbbotSyntax.Binding name =>
          (if Set.find sorts name
           then SortBinding name
           else if Set.find symbs name
           then SymbolBinding name
           else raise Fail (name ^ " is not a sort or symbol, so it cannot be bound.")) (*???location*)
        | AbbotSyntax.Prod aritys =>
          Prod (List.map (convert_sort_arity (exts, symbs, abts, sorts)) aritys)
        | AbbotSyntax.App ("list", [arity]) =>
          List (convert_sort_arity (exts, symbs, abts, sorts) arity)
        | AbbotSyntax.App (name, aritys) =>
          (if Set.find exts name
           then
             AppExt
               (name,
                List.map
                  (convert_sort_arity (exts, symbs, abts, sorts))
                  aritys)
           else if Set.find abts name
           then
             AppAbt
               (name,
                List.map
                  (convert_sort_arity (exts, symbs, abts, sorts))
                  aritys)
           else raise Fail (name ^ " is not a defined abt.")) (*???location*)
        | AbbotSyntax.Dot (binding, arity) =>
          Dot
            (convert_sort_arity (exts, symbs, abts, sorts) binding,
             convert_sort_arity (exts, symbs, abts, sorts) arity)

  fun sort_arity_binds abts arity =
      case arity of
          (SymbolUse _ | SortUse _) => false
        | (SymbolBinding _ | SortBinding _) => true
        | List arity => sort_arity_binds abts arity
        | (Prod aritys | AppExt (_, aritys)) =>
          List.exists (sort_arity_binds abts) aritys
        | AppAbt (abt, aritys) =>
          List.exists (sort_arity_binds abts) aritys
          orelse
          let val (args, opers) = valOf (find abts abt) in
            List.exists
              (fn (_, arity_opt) =>
                  case arity_opt of
                      NONE => false
                    | SOME arity => abt_arity_binds abt abts arity)
              opers
          end
        | Dot (_, arity) => sort_arity_binds abts arity
  end

  local open AbtArity in
  fun abt_arity_deps arity =
      case arity of
          (Param _ | SymbolUse _ | SymbolBinding _) =>
          (Set.empty (), Set.empty ())
        | (SortUse srt | SortBinding srt) => (Set.empty (), Set.singleton srt)
        | Prod aritys =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.empty (), Set.empty ())
            (List.map abt_arity_deps aritys)
        | List arity =>
          abt_arity_deps arity
        | AppExt (ext, aritys) =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.empty (), Set.empty ())
            (List.map abt_arity_deps aritys)
        | AppAbt (abt, aritys) =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.singleton abt, Set.empty ())
            (List.map abt_arity_deps aritys)
        | Dot (binding, arity) =>
          let
            val (abts1, sorts1) = abt_arity_deps binding
            val (abts2, sorts2) = abt_arity_deps arity
          in
            (Set.union (abts1, abts2), Set.union (sorts1, sorts2))
          end
  end

  local open SortArity in
  fun sort_arity_deps arity =
      case arity of
          (SortUse srt | SortBinding srt) => (Set.empty (), Set.singleton srt)
        | (SymbolUse _ | SymbolBinding _) => (Set.empty (), Set.empty ())
        | Prod aritys =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.empty (), Set.empty ())
            (List.map sort_arity_deps aritys)
        | List arity =>
          sort_arity_deps arity
        | AppExt (ext, aritys) =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.empty (), Set.empty ())
            (List.map sort_arity_deps aritys)
        | AppAbt (abt, aritys) =>
          List.foldl
            (fn ((abts1, sorts1), (abts2, sorts2)) =>
                (Set.union (abts1, abts2), Set.union (sorts1, sorts2)))
            (Set.singleton abt, Set.empty ())
            (List.map sort_arity_deps aritys)
        | Dot (binding, arity) =>
          let
            val (abts1, sorts1) = sort_arity_deps binding
            val (abts2, sorts2) = sort_arity_deps arity
          in
            (Set.union (abts1, abts2), Set.union (sorts1, sorts2))
          end
  end

  local open AbtArity in
  fun sorts_bound_in_abt_arity arity =
      case arity of
          (Param _ | SortUse _ | SymbolUse _ | SymbolBinding _) => Set.empty ()
        | SortBinding srt => Set.singleton srt
        | List arity =>
          sorts_bound_in_abt_arity arity
        | (Prod aritys | AppExt (_, aritys) | AppAbt (_, aritys)) =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_bound_in_abt_arity aritys)
        | Dot (binding, arity) =>
          Set.union
            (sorts_bound_in_abt_arity binding, sorts_bound_in_abt_arity arity)
  end

  local open SortArity in
  fun sorts_bound_in_sort_arity arity =
      case arity of
          (SortUse _ | SymbolUse _ | SymbolBinding _) => Set.empty ()
        | SortBinding srt => Set.singleton srt
        | List arity =>
          sorts_bound_in_sort_arity arity
        | (Prod aritys | AppExt (_, aritys) | AppAbt (_, aritys)) =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_bound_in_sort_arity aritys)
        | Dot (binding, arity) =>
          Set.union
            (sorts_bound_in_sort_arity binding, sorts_bound_in_sort_arity arity)
  end

  local open AbtArity in
  fun abt_arity_haslist arity =
      case arity of
          (Param _
          | SortUse _
          | SymbolUse _
          | SortBinding _
          | SymbolBinding _) => false
        | List arity => true
        | (Prod aritys | AppExt (_, aritys) | AppAbt (_, aritys)) =>
          List.exists abt_arity_haslist aritys
        | Dot (binding, arity) =>
          abt_arity_haslist binding orelse abt_arity_haslist arity
  end

  local open SortArity in
  fun sort_arity_haslist arity =
      case arity of
          (SortUse _
          | SymbolUse _
          | SortBinding _
          | SymbolBinding _) => false
        | List arity => true
        | (Prod aritys | AppExt (_, aritys) | AppAbt (_, aritys)) =>
          List.exists sort_arity_haslist aritys
        | Dot (binding, arity) =>
          sort_arity_haslist binding orelse sort_arity_haslist arity
  end

  fun analyze (exts, symbs, abts, sorts) : ana =
      let
        fun string_to_abt_or_sort str =
            case find abts str of
                SOME _ => SOME (Abt str)
              | NONE =>
                (case find sorts str of
                     SOME _ => SOME (Sort str)
                   | NONE => NONE)

        val set_to_list = Seq.toList o Set.toSeq

        val all_names = (domain exts, symbs, domain abts, domain sorts)

        val abts =
            map
              (fn (args, opers) =>
                  (args,
                   List.map
                     (fn (oper, arity_opt) =>
                         (oper,
                          (case arity_opt of
                               NONE => NONE
                             | SOME arity =>
                               SOME (convert_abt_arity all_names arity))))
                     opers))
              abts

        val args = #1 o valOf o find abts

        val sorts =
            map
              (List.map
                 (fn (oper, arity_opt) =>
                     (oper,
                      (case arity_opt of
                           NONE => NONE
                         | SOME arity =>
                           let
                             val arity' = convert_sort_arity all_names arity
                           in
                             if sort_arity_binds abts arity'
                             then raise Fail "All bindings must come before a dot" (*???location*)
                             else SOME arity'
                           end))))
              sorts

        val haslist =
            List.exists
              (fn (_, opers) =>
                  List.exists
                    (fn (oper, arity_opt) =>
                        case arity_opt of
                            NONE => false
                          | SOME arity =>
                            abt_arity_haslist arity)
                    opers)
              (Seq.toList (range abts))
            orelse
            List.exists
              (List.exists
                 (fn (_, arity_opt) =>
                     case arity_opt of
                         NONE => false
                       | SOME arity =>
                         sort_arity_haslist arity))
              (Seq.toList (range sorts))

        local
          fun neighbors G F =
              Seq.reduce Set.union (Set.empty ()) (range (extract (G, F)))

          fun bfs G frontier visited =
             if Set.size frontier = 0
             then visited
             else let
               val visited' = Set.union (visited, frontier)
               val frontier' = Set.difference (neighbors G frontier, visited')
             in
               bfs G frontier' visited'
             end

          val direct_abt_dep_table =
              map
                (fn (args, opers) =>
                    List.foldl Set.union (Set.empty ())
                      (List.map
                         (fn (oper, arity_opt) =>
                             case arity_opt of
                                 NONE => Set.empty ()
                               | SOME arity =>
                                 Set.union (abt_arity_deps arity))
                         opers))
                abts

          val direct_sort_dep_table =
              map
                (fn opers =>
                    List.foldl Set.union (Set.empty ())
                      (List.map
                         (fn (oper, arity_opt) =>
                             case arity_opt of
                                 NONE => Set.empty ()
                               | SOME arity =>
                                 Set.union (sort_arity_deps arity))
                         opers))
                sorts

          val direct_dep_table =
              merge
                (fn (_, _) => raise Fail "Found abt and sort with the same name.")
                (direct_abt_dep_table, direct_sort_dep_table)
        in
        val merged_dep_table =
            mapk
              (fn (srt, _) =>
                  bfs direct_dep_table (Set.singleton srt) (Set.singleton srt))
              direct_dep_table

        val dep_table =
            map
              (fn deps =>
                  (Set.filter
                     (fn str =>
                         case string_to_abt_or_sort str of
                             SOME (Abt _) => true
                           | SOME (Sort _) => false
                           | NONE => raise Fail "Internal Abbot Error")
                     deps,
                   Set.filter
                     (fn str =>
                         case string_to_abt_or_sort str of
                             SOME (Abt _) => false
                           | SOME (Sort _) => true
                           | NONE => raise Fail "Internal Abbot Error")
                     deps))
              merged_dep_table
        end

        fun dependson (Abt str | Sort str) abt_or_sort =
            let val SOME (abts, sorts) = find dep_table str in
              case abt_or_sort of
                  Abt abt => Set.find abts abt
                | Sort sort => Set.find sorts sort
            end

        fun dependencies (Abt str | Sort str) =
            let val SOME (abts, sorts) = find dep_table str in
              (set_to_list abts, set_to_list sorts)
            end

        val hasvar_set =
            Set.union
              (reduce Set.union (Set.empty ())
                 (map
                    (fn (args, opers) =>
                        List.foldl Set.union (Set.empty ())
                          (List.map
                             (fn (_, arity_opt) =>
                                 case arity_opt of
                                     NONE => Set.empty ()
                                   | SOME arity =>
                                     sorts_bound_in_abt_arity arity)
                             opers))
                         abts),
               reduce Set.union (Set.empty ())
                 (map
                    (fn opers =>
                        List.foldl Set.union (Set.empty ())
                          (List.map
                             (fn (_, arity_opt) =>
                                 case arity_opt of
                                     NONE => Set.empty ()
                                   | SOME arity =>
                                     sorts_bound_in_sort_arity arity)
                             opers))
                    sorts))

        val hasvar = Set.find hasvar_set

        val mutual_table =
            mapk
              (fn (s, (abt_deps, sort_deps)) =>
                  let
                    val abts =
                        Set.filter
                          (fn s' => Set.find (valOf (find merged_dep_table s')) s)
                          abt_deps

                    val sorts =
                        Set.filter
                          (fn s' =>
                              case find merged_dep_table s' of
                                  NONE => raise Fail "bar"
                                | SOME set => Set.find set s)
                          sort_deps
                  in
                    case valOf (string_to_abt_or_sort s) of
                        Abt abt =>
                        (Set.insert abt abts, sorts)
                      | Sort sort =>
                        (abts, Set.insert sort sorts)
                  end)
              dep_table

        fun mutual' (Abt s | Sort s) =
            valOf (find mutual_table s)

        fun mutual abt_or_sort =
            let val (abts, sorts) = mutual' abt_or_sort in
              (set_to_list abts, set_to_list sorts)
            end

        fun mutualwith s1 s2 =
            let val (abts, sorts) = mutual' s1 in
              case s2 of
                  Abt abt => Set.find abts abt
                | Sort sort => Set.find sorts sort
            end

        local open Sum2 in
        val abts_and_sorts =
            Seq.iter
              (fn (ls, s) =>
                  if
                    (case s of
                         Abt abt =>
                         List.exists
                           (List.exists (fn In1 (x, _) => x = abt | _ => false))
                           ls
                       | Sort sort =>
                         List.exists
                           (List.exists (fn In2 (x, _) => x = sort | _ => false))
                           ls)
                  then ls
                  else
                    let val (mut_abts, mut_sorts) = mutual s in
                      (List.map
                         (fn s' => In1 (s', valOf (find abts s')))
                         mut_abts
                       @ List.map
                           (fn s' => In2 (s', valOf (find sorts s')))
                           mut_sorts)
                      :: ls
                    end)
              []
              (Seq.append
                 (Seq.map Abt (Set.toSeq (domain abts)),
                  Seq.map Sort (Set.toSeq (domain sorts))))

        fun group_compare ((In1 (l, _) | In2 (l, _))::ls, (In1 (r, _) | In2 (r, _))::rs) =
            let
              val lgeqr =
                  case find merged_dep_table l of
                      NONE => false
                    | SOME deps => Set.find deps r
              val rgeql =
                  case find merged_dep_table r of
                      NONE => false
                    | SOME deps => Set.find deps l
            in
              if lgeqr
              then GREATER
              else if rgeql
              then LESS
              else EQUAL
            end
        end

        val abts_and_sorts =
            Seq.toList (Seq.sort group_compare (Seq.fromList (abts_and_sorts)))
      in
        {
          externals = Seq.toList (toSeq exts),
          symbols=set_to_list symbs,
          abts_and_sorts=abts_and_sorts,
          haslist=haslist,
          dependencies=dependencies,
          dependson=dependson,
          args=args,
          hasvar=hasvar,
          mutual=mutual,
          mutualwith=mutualwith
        }
      end
end
