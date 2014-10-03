structure Analysis =
struct
  open Syntax

  datatype mappable
    = MappableVar of string
    | ProdMappable of mappable list
    | ExternalMappable of string * mappable list

  datatype iterable
    = IterableVar of string
    | ProdIterable of iterable list
    | ExternalIterable of string * iterable list

  datatype arity
    = Sort of string
    | Symbol of string
    | Binding of iterable * string list * mappable * arity list

  type ana = {
    (* All sorts in dependency order and with mutual dependencies grouped.
     * ??? Dependency does not consider binding. *)
    sorts : string list list,

    (* Returns true iff the given string is a valid sort. *)
    issrt : string -> bool,

    (* All symbols. *)
    symbs : string list,

    (* Returns true iff the given string is a valid symbol. *)
    issym : string -> bool,

    (* Maps sorts to a list of their operators. *)
    opers : string -> string list,

    (* Maps a sort and operator to the operator's arity. *)
    arity : string -> string -> (string list * string) list,

    (* binds sry srt_or_sym:
     * If srt_or_sym is a sort, returns true iff variables of sort srt_or_sym
     *  can be bound by srt.
     * If srt_or_sym is a symbol, returns true iff the symbol srt_or_sym can be
     *  bound by srt. *)
    binds : string -> string -> bool,

    (* Returns a list of the sorts of variables that can be found in the given
     * sort or any sort it contains. *)
    varin : string -> string list,

    (* Returns a list of the symbols that can be found in the given sort or any
     * sort it contains. *)
    symin : string -> string list,

    (* Returns all the mutually dependent sorts of a given sort,
     * including itself *)
    mutual : string -> string list,

    (* Returns true iff the given sorts are mutually dependent. *)
    mutualwith : string -> string -> bool
  }

  fun analyze (parse_data : Syntax.oper list StringTable.table * string list) : ana =
      let
        open StringTable

        val (sorts, symbs) = parse_data

        fun issrt s =
            case find sorts s of
                NONE => false
              | SOME _ => true

        fun issym s =
            List.exists (fn a => a = s) symbs

        fun opers s =
            List.map #name (valOf (find sorts s))

        fun arity s oper =
            #arity
              (valOf
                 (List.find
                    (fn {name, arity} => name = oper)
                    (valOf (find sorts s))))

        val binding_table =
            map
              (fn opers =>
                  List.foldl Set.union (Set.empty ())
                    (List.map
                       (fn {name, arity} =>
                           List.foldl Set.union (Set.empty ())
                             (List.map
                                (Set.fromSeq o Seq.fromList o #1)
                                arity))
                       opers))
              sorts

        fun binds s1 s2 =
            case find binding_table s1 of
                NONE => false
              | SOME bound => Set.find bound s2

        val set_to_list = Seq.toList o Set.toSeq

        val depsym_table =
            map
              (fn opers =>
                  List.foldl
                    Set.union
                    (Set.empty ())
                    (List.map
                       (fn {name, arity} =>
                           List.foldl
                             Set.union
                             (Set.empty ())
                             (List.map
                                (Set.singleton o #2)
                                arity))
                       opers))
              sorts

        local
          open StringTable

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

          (* Should this also consider bindings??? *)
          val simple_dep_table =
              map (Set.filter issrt) depsym_table
        in
        val dep_table =
            mapk
              (fn (srt, _) =>
                  Set.insert
                    srt
                    (bfs simple_dep_table (Set.singleton srt) (Set.empty ())))
              sorts
        end

        fun hasvar srt =
            List.exists
              (fn srt' => binds srt' srt)
              (Seq.toList (Set.toSeq (domain sorts)))

        val varin = List.filter hasvar o set_to_list o valOf o find dep_table

        val simple_sym_table = map (Set.filter issym) depsym_table

        val sym_table =
            map
              (fn srts =>
                  Seq.reduce
                    Set.union
                    (Set.empty ())
                    (Seq.map
                       (valOf o find simple_sym_table)
                       (Set.toSeq srts)))
              dep_table

        val symin = set_to_list o valOf o find sym_table

        val mutual_table =
            mapk
              (fn (s, varsin) =>
                  Set.insert s
                    (Set.filter
                       (fn s' =>
                           case find dep_table s' of
                               NONE => false
                             | SOME varsin' =>
                               Set.find varsin' s)
                       varsin))
              dep_table

        fun mutual' s =
            find mutual_table s

        val mutual = set_to_list o valOf o mutual'

        fun mutualwith s1 s2 =
            case mutual' s1 of
                NONE => false
              | SOME mutuals => Set.find mutuals s2

        val sorts =
            Seq.iter
              (fn (ls, s) =>
                  if List.exists (List.exists (fn x => x = s)) ls
                  then ls
                  else mutual s::ls)
              []
              (Set.toSeq (domain sorts))

        fun sort_group_compare (l::ls, r::rs) =
            let
              val lgeqr =
                  case find dep_table l of
                      NONE => false
                    | SOME deps => Set.find deps r
              val rgeql =
                  case find dep_table r of
                      NONE => false
                    | SOME deps => Set.find deps l
            in
              if lgeqr
              then GREATER
              else if rgeql
              then LESS
              else EQUAL
            end

        val sorts =
            Seq.toList (Seq.sort sort_group_compare (Seq.fromList sorts))

      in
        {
          sorts=sorts,
          issrt=issrt,
          symbs=symbs,
          issym=issym,
          opers=opers,
          arity=arity,
          binds=binds,
          varin=varin,
          symin=symin,
          mutual=mutual,
          mutualwith=mutualwith
        }
      end
end
