functor MkLeftistHeapPQ(structure OrdKey : ORDKEY) : PQUEUE =
struct
  structure Key = OrdKey

  datatype 'a pq =
      EMPTY
    | NODE of {rank : int, size : int, data : Key.t * 'a, left : 'a pq, right : 'a pq}

  type key = Key.t
  type 'a t = 'a pq

  fun empty () = EMPTY

  fun isEmpty EMPTY = true
    | isEmpty _ = false

  fun rank EMPTY = 0
    | rank (NODE {rank, ...}) = rank

  fun size EMPTY = 0
    | size (NODE {size, ...}) = size

  fun mkNode (d, l, r) =
      if rank r < rank l
      then NODE {rank=1 + rank r, size=(size l) + (size r) + 1, data=d, left=l, right=r}
      else NODE {rank=1 + rank l, size=(size l) + (size r) + 1, data=d, left=r, right=l}

  fun singleton kv = mkNode (kv, EMPTY, EMPTY)
  val $ = singleton

  fun meld ((x, EMPTY) | (EMPTY, x)) = x
    | meld (n1 as NODE {data=d1 as (k1,_), left=l1, right=r1, ...},
            n2 as NODE {data=d2 as (k2,_), left=l2, right=r2, ...}) =
      case Key.compare (k1, k2)
        of LESS => mkNode (d1, l1, meld (r1, n2))
         | _ => mkNode (d2, l2, meld (n1, r2))

  fun insert kv Q = meld (singleton kv, Q)

  fun fromList [] = empty ()
    | fromList (x::xs) = insert x (fromList xs)
  val % = fromList

  fun findMin EMPTY = NONE
    | findMin (NODE {data=kv, ...}) = SOME kv

  fun deleteMin EMPTY = (NONE, EMPTY)
    | deleteMin (NODE {data=kv, left=l, right=r, ...}) = (SOME kv, meld (l, r))
end
