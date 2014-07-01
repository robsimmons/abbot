functor MkTreap(structure HashKey : HASHKEY) : BSTREE =
struct
  structure Key = HashKey

  type key = Key.t
  type priority = int
  type 'a data = { key : key, value : 'a, pri : priority }

  datatype 'a treap =
      EMPTY
    | NODE of { size : int,
                data : 'a data,
                left : 'a treap,
                right : 'a treap }

  type 'a bst = 'a treap
  type 'a node = { key : key, value : 'a, left : 'a bst, right : 'a bst }

  fun size EMPTY = 0
    | size (NODE {size, ...}) = size

  fun empty () = EMPTY

  fun singleton (k, v) =
      NODE {size=1, data={key=k, value=v, pri=HashKey.hash k},
            left=EMPTY, right=EMPTY}

  local
    fun mk (d, l, r) =
        NODE {size=1 + size l + size r, data=d, left=l, right=r}
  in
    fun join ((EMPTY, t) | (t, EMPTY)) = t
      | join (nL as NODE {data=dL, left=lL, right=rL, ...},
              nR as NODE {data=dR, left=lR, right=rR, ...}) =
        if #pri dL < #pri dR
        then mk (dL, lL, join (rL, nR))
        else mk (dR, join (nL, lR), rR)

    fun splitAt (t, k) =
        let
          fun spl EMPTY f = f (EMPTY, NONE, EMPTY)
            | spl (NODE {data=d, left=l, right=r, ...}) f =
              case HashKey.compare (k, #key d)
                of EQUAL => f (l, SOME (#value d), r)
                 | LESS => spl l (fn (L, M, R) => f (L, M, mk (d, R, r)))
                 | GREATER => spl r (fn (L, M, R) => f (mk (d, l, L), M, R))
        in spl t (fn x => x)
        end
  end

  fun expose EMPTY = NONE
    | expose (NODE {data={key=k, value=v, ...}, left=l, right=r, ...}) =
      SOME {key=k, value=v, left=l, right=r}

  val $ = singleton
  fun makeNode {left, key, value, right} =
      join (left, join ($ (key, value), right))
end
