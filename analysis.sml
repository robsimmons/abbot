structure Analysis :> sig
  datatype ('sym, 'ast, 'srt) binding
    = SortBinding of 'srt
    | SymbolBinding of 'sym
    | ProdBinding of ('sym, 'ast, 'srt) binding list
    | ListBinding of ('sym, 'ast, 'srt) binding
    | AppBinding of 'ast * ('sym, 'ast, 'srt) binding list

  datatype ('sym, 'ast, 'srt) arity
    = SortArity of 'srt
    | SymbolArity of 'sym
    | ProdArity of ('sym, 'ast, 'srt) arity list
    | ListArity of ('sym, 'ast, 'srt) arity
    | AppArity of 'ast * ('sym, 'ast, 'srt) arity list
    | BindingArity of ('sym, 'ast, 'srt) binding * ('sym, 'ast, 'srt) arity

  datatype 'ast ast_arity
    = Param of string
    | ProdAstArity of 'ast ast_arity list
    | AppAstArity of 'ast * 'ast ast_arity list
    | ListAstArity of 'ast ast_arity

  eqtype symbol

  val sym_to_string : symbol -> string

  eqtype ast

  val ast_to_string : ast -> string

  eqtype sort

  val sort_to_string : sort -> string

  type ana = {
    (* All symbols. *)
    symbs : symbol list,

    (* ??? Missing ast arity. *)
    asts : (ast * (string list * (string * ast ast_arity option) list)) list,

    (* Whether the list ast structure needs to be included. *)
    haslist : bool,

    (* All sorts and their associated operations and aritys.
     * Sorts are grouped with their mutual dependencies and occur
     * later in the outer list than their strict dependencies. *)
    sorts : (sort * (string * (symbol, ast, sort) arity option) list) list list,

    (* Sorts that the given sort refers to. *)
    dependencies : sort -> sort list,

    (* Whether the given sort can be bound to a variable. *)
    hasvar : sort -> bool,

    (* Returns all the mutually dependent sorts of a given sort,
     * including itself *)
    mutual : sort -> sort list,

    (* Returns true iff the given sorts are mutually dependent. *)
    mutualwith : sort -> sort -> bool
  }

  val analyze : AbtSyntax.oper list StringTable.table
                * string list
                * (string list * AbtSyntax.ast_oper list) StringTable.table
                -> ana
end = struct
  open Util
  open StringTable

  datatype ('sym, 'ast, 'srt) binding
    = SortBinding of 'srt
    | SymbolBinding of 'sym
    | ProdBinding of ('sym, 'ast, 'srt) binding list
    | ListBinding of ('sym, 'ast, 'srt) binding
    | AppBinding of 'ast * ('sym, 'ast, 'srt) binding list

  datatype ('sym, 'ast, 'srt) arity
    = SortArity of 'srt
    | SymbolArity of 'sym
    | ProdArity of ('sym, 'ast, 'srt) arity list
    | ListArity of ('sym, 'ast, 'srt) arity
    | AppArity of 'ast * ('sym, 'ast, 'srt) arity list
    | BindingArity of ('sym, 'ast, 'srt) binding * ('sym, 'ast, 'srt) arity

  datatype 'ast ast_arity
    = Param of string
    | ProdAstArity of 'ast ast_arity list
    | AppAstArity of 'ast * 'ast ast_arity list
    | ListAstArity of 'ast ast_arity

  type symbol = string

  fun sym_to_string x = x

  type ast = string

  fun ast_to_string x = x

  type sort = string

  fun sort_to_string x = x

  type ana = {
    symbs : symbol list,
    asts : (ast * (string list * (string * ast ast_arity option) list)) list,
    haslist : bool,
    sorts : (sort * (string * (symbol, ast, sort) arity option) list) list list,
    dependencies : sort -> sort list,
    hasvar : sort -> bool,
    mutual : sort -> sort list,
    mutualwith : sort -> sort -> bool
  }

  fun convert_binding (sorts, symbs) binding =
      case binding of
          AbtSyntax.BindingVar name =>
          (if List.exists (fn x => x = name) sorts
           then SortBinding name
           else if List.exists (fn x => x = name) symbs
           then SymbolBinding name
           else AppBinding (name, []))
        | AbtSyntax.ProdBinding bindings =>
          ProdBinding (List.map (convert_binding (sorts, symbs)) bindings)
        | AbtSyntax.AppBinding ("list", [binding]) =>
          ListBinding (convert_binding (sorts, symbs) binding)
        | AbtSyntax.AppBinding (ast, bindings) =>
          AppBinding (ast, List.map (convert_binding (sorts, symbs)) bindings)

  fun convert_arity (sorts, symbs) arity =
      case arity of
          AbtSyntax.ArityVar name =>
          (if List.exists (fn x => x = name) sorts
           then SortArity name
           else if List.exists (fn x => x = name) symbs
           then SymbolArity name
           else AppArity (name, []))
        | AbtSyntax.ProdArity aritys =>
          ProdArity (List.map (convert_arity (sorts, symbs)) aritys)
        | AbtSyntax.AppArity ("list", [arity]) =>
          ListArity (convert_arity (sorts, symbs) arity)
        | AbtSyntax.AppArity (ast, aritys) =>
          AppArity (ast, List.map (convert_arity (sorts, symbs)) aritys)
        | AbtSyntax.BindingArity (binding, arity) =>
          BindingArity
            (convert_binding (sorts, symbs) binding,
             convert_arity (sorts, symbs) arity)

  fun convert_ast_arity ast_arity =
      case ast_arity of
          AbtSyntax.Param str => Param str
        | AbtSyntax.ProdAstArity ast_aritys =>
          ProdAstArity (List.map convert_ast_arity ast_aritys)
        | AbtSyntax.AppAstArity ("list", [ast_arity]) =>
          ListAstArity (convert_ast_arity ast_arity)
        | AbtSyntax.AppAstArity (ast, ast_aritys) =>
          AppAstArity (ast, List.map convert_ast_arity ast_aritys)

  fun sorts_in_binding binding =
      case binding of
          SortBinding srt => Set.singleton srt
        | SymbolBinding sym => Set.empty ()
        | ProdBinding bindings =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_in_binding bindings)
        | ListBinding binding =>
          sorts_in_binding binding
        | AppBinding (ast, bindings) =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_in_binding bindings)

  fun sorts_in_arity arity =
      case arity of
          SortArity srt => Set.singleton srt
        | SymbolArity sym => Set.empty ()
        | ProdArity aritys =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_in_arity aritys)
        | ListArity arity =>
          sorts_in_arity arity
        | AppArity (ast, aritys) =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_in_arity aritys)
        | BindingArity (binding, arity) =>
          Set.union
            (sorts_in_binding binding,
             sorts_in_arity arity)

  fun sorts_bound_in_arity arity =
      case arity of
          SortArity srt => Set.empty ()
        | SymbolArity sym => Set.empty ()
        | ProdArity aritys =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_bound_in_arity aritys)
        | ListArity arity =>
          sorts_bound_in_arity arity
        | AppArity (ast, aritys) =>
          List.foldl Set.union (Set.empty ())
            (List.map sorts_bound_in_arity aritys)
        | BindingArity (binding, arity) =>
          Set.union
            (sorts_in_binding binding,
             sorts_bound_in_arity arity)

  fun binding_haslist binding =
      case binding of
          (SortBinding _ | SymbolBinding _) => false
        | ListBinding _ => true
        | (ProdBinding bindings | AppBinding (_, bindings)) =>
          List.exists binding_haslist bindings

  fun arity_haslist arity =
      case arity of
          (SortArity _ | SymbolArity _) => false
        | ListArity _ => true
        | (ProdArity aritys | AppArity (_, aritys)) =>
          List.exists arity_haslist aritys
        | BindingArity (binding, arity) =>
          binding_haslist binding orelse arity_haslist arity

  fun ast_arity_haslist arity =
      case arity of
          Param _ => false
        | ListAstArity _ => true
        | (ProdAstArity aritys | AppAstArity (_, aritys)) =>
          List.exists ast_arity_haslist aritys

  fun analyze (sorts, symbs, asts) : ana =
      let
        val asts =
            Seq.toList
              (toSeq
                 (map
                    (fn (args, opers) =>
                        (args,
                         List.map
                           (fn (oper, ast_arity_opt) =>
                               (oper,
                                (case ast_arity_opt of
                                     NONE => NONE
                                   | SOME ast_arity =>
                                     SOME (convert_ast_arity ast_arity))))
                           opers))
                    asts))

        val set_to_list = Seq.toList o Set.toSeq

        val sorts =
            map
              (fn opers =>
                  List.map
                    (fn (oper, arity_opt) =>
                        (oper,
                         (case arity_opt of
                              NONE => NONE
                            | SOME arity =>
                              SOME
                                (convert_arity
                                   (set_to_list (domain sorts), symbs)
                                   arity))))
                    opers)
              sorts

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

          val direct_dep_table =
              map
                (fn opers =>
                    List.foldl Set.union (Set.empty ())
                      (List.map
                         (fn (oper, arity_opt) =>
                             case arity_opt of
                                 NONE => Set.empty ()
                               | SOME arity =>
                                 sorts_in_arity arity)
                         opers))
                sorts
        in
        val dep_table =
            mapk
              (fn (srt, _) =>
                  Set.insert
                    srt
                    (bfs direct_dep_table (Set.singleton srt) (Set.empty ())))
              sorts
        end

        val dependencies = set_to_list o valOf o find dep_table

        val hasvar_set =
            reduce Set.union (Set.empty ())
              (map
                 (fn opers =>
                     List.foldl Set.union (Set.empty ())
                       (List.map
                          (fn (_, arity_opt) =>
                              case arity_opt of
                                  NONE => Set.empty ()
                                | SOME arity =>
                                  sorts_bound_in_arity arity)
                          opers))
                 sorts)

        val hasvar = Set.find hasvar_set

        val mutual_table =
            mapk
              (fn (s, deps) =>
                  Set.insert s
                    (Set.filter
                       (fn s' => Set.find (valOf (find dep_table s')) s)
                       deps))
              dep_table

        fun mutual' s =
            valOf (find mutual_table s)

        val mutual = set_to_list o mutual'

        fun mutualwith s1 s2 =
            Set.find (mutual' s1) s2

        val sorts =
            Seq.iter
              (fn (ls, s) =>
                  if List.exists (List.exists (fn (x, _) => x = s)) ls
                  then ls
                  else
                    List.map (fn s' => (s', valOf (find sorts s'))) (mutual s)
                    :: ls)
              []
              (Set.toSeq (domain sorts))

        fun sort_group_compare ((l, _)::ls, (r, _)::rs) =
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
          | sort_group_compare _ = raise Fail "Internal Abbot Error"

        val sorts =
            Seq.toList (Seq.sort sort_group_compare (Seq.fromList sorts))

        val haslist =
            List.exists
              (fn (_, (_, opers)) =>
                  List.exists
                    (fn (oper, arity_opt) =>
                        case arity_opt of
                            NONE => false
                          | SOME arity =>
                            ast_arity_haslist arity)
                    opers)
              asts
            orelse
            List.exists
              (List.exists
                 (fn (_, opers) =>
                     List.exists
                       (fn (_, arity_opt) =>
                           case arity_opt of
                               NONE => false
                             | SOME arity =>
                               arity_haslist arity)
                       opers))
              sorts
      in
        {
          symbs=symbs,
          asts=asts,
          haslist=haslist,
          sorts=sorts,
          dependencies=dependencies,
          hasvar=hasvar,
          mutual=mutual,
          mutualwith=mutualwith
        }
      end
end
