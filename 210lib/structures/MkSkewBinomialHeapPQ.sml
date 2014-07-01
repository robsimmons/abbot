functor MkSkewBinomialHeapPQ(structure OrdKey : ORDKEY) : PQUEUE =
struct
  structure Key = OrdKey

  type key = Key.t

  fun compare ((l, _) : key * 'a, (r, _) : key * 'a) : order =
      Key.compare (l, r)

  (* A binomial tree *)
  (* data is the key value pair at the node. *)
  (* extra is extra key value pairs, all of which
   * are less than or equal to the data at the node. *)
  (* children is the children of the node. The ranks
   * of the children must be in decreasing order and
   * all be less than the rank of the node. The data of
   * the children must also be less than the data at the
   * node. *)
  datatype 'a btree = Node of {data : key * 'a,
                               extra : (key * 'a) list,
                               children : 'a btree list}

  (* The rank of a binomial tree is its number of children *)
  fun rank (Node {children, ...}) = List.length children

  fun data (Node {data, ...}) = data

  (* Make a tree of higher rank a child of a tree with lower rank. *)
  fun link (t1 as Node {data=x1, extra=xs1, children=c1},
            t2 as Node {data=x2, extra=xs2, children=c2}) =
      case compare (x1, x2) of
          (LESS | EQUAL) => Node {data=x1, extra=xs1, children=t2::c1}
        | GREATER        => Node {data=x2, extra=xs2, children=t1::c2}

  (* link two trees and then add x to their data *)
  fun skewLink x (t1, t2) =
      let val Node {data=y, extra=ys, children=c} = link (t1, t2)
      in case compare (x, y) of
              (LESS | EQUAL) => Node {data=x, extra=y::ys, children=c}
            | GREATER        => Node {data=y, extra=x::ys, children=c}
      end

  (* A skew binomial heap *)
  (* trees must be a list of binomial trees whose
   * ranks form a binary or skew binary number.
   * This means all of the ranks must be unique
   * except for the lowest rank which can occur
   * at most twice. Also the ranks must be in
   * increasing order. *)
  type 'a pq = {trees : 'a btree list,
                min : (key * 'a) option,
                size : int}

  type 'a t = 'a pq

  fun empty () = {trees=[], min=NONE, size=0}

  fun isEmpty {trees=[], min=NONE, size=0} = true
    | isEmpty _ = false

  fun size (q : 'a pq) = #size q

  fun singleton x =
      {trees=[Node {data=x, extra=[], children=[]}],
       min=SOME x,
       size=1}

  val $ = singleton

  fun optionMin ((m, NONE) | (NONE, m)) = m
    | optionMin (SOME l, SOME r) =
      (case compare (l, r) of
           LESS => SOME l
         | _ => SOME r)

  (* Insert a tree into list of trees whose ranks form
   * a binary number *)
  fun insTree t ts =
      case ts of
          [] => [t]
        | t'::ts' =>
          if rank t < rank t'
          then t::ts
          else insTree (link (t, t')) ts'

  (* Merge two lists of trees preserving rank ordering. *)
  fun mergeTrees ((ts, []) | ([], ts)) = ts
    | mergeTrees (t1::ts1, t2::ts2) =
      case Int.compare (rank t1, rank t2) of
          LESS => t1 :: (mergeTrees (ts1, t2::ts2))
        | EQUAL => insTree (link (t1, t2)) (mergeTrees (ts1, ts2))
        | GREATER => t2 :: (mergeTrees (t1::ts1, ts2))

  (* If the tree ranks form a skew binary number,
   * change them to a binary number. *)
  fun normalize [] = []
    | normalize (t::ts) = insTree t ts

  fun insert x {trees=ts, min=m, size=s} =
      {trees=case ts of
                 t1::t2::ts' =>
                 if rank t1 = rank t2
                 then skewLink x (t1, t2) :: ts'
                 else Node {data=x, extra=[], children=[]} :: ts
               | _ => Node {data=x, extra=[], children=[]} :: ts,
       min=optionMin (SOME x, m),
       size=s + 1}

  fun insertList [] ts = ts
    | insertList (x::xs) ts = insertList xs (insert x ts)

  fun fromList l = insertList l (empty ())
  val % = fromList

  fun meld ({trees=ts1, min=m1, size=s1}, {trees=ts2, min=m2, size=s2}) =
      {trees=mergeTrees (normalize ts1, normalize ts2),
       min=optionMin (m1, m2),
       size=s1 + s2}

  fun findMin ({min, ...} : 'a pq) = min

  local
    (* Find the tree with the minimum element and remove it so that
     * we remove and return its root and then add the rest of the tree
     * back into the priority queue. *)
    fun getMin [] = NONE
      | getMin (t::ts) =
        case getMin ts of
            NONE => SOME (t, ts)
          | SOME (t', ts') =>
            (case compare (data t, data t') of
                 (LESS | EQUAL) => SOME (t, ts)
               | GREATER => SOME (t', t :: ts'))

    (* Find the min by searching the roots of the trees. We need to do
     * this to pre-calculate the result of findMin. *)
    fun calculateMin [] = NONE
      | calculateMin (t::ts) = optionMin (calculateMin ts, SOME (data t))
  in
  fun deleteMin (q as {trees=ts, min=_, size=s}) =
      case getMin ts of
          NONE => (NONE, q)
        | SOME (Node {data=x, extra=xs, children=c}, ts') =>
          (SOME x,
           let val ts'' = mergeTrees (rev c, normalize ts')
           in insertList xs
                         {trees=ts'',
                          min=calculateMin ts'',
                          size=s - (List.length xs) - 1}
           end)
  end
end
