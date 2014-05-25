structure ListSequence : SEQUENCE =
struct
  open List

  type 'a seq = 'a list
  type 'a ord = 'a * 'a -> order

  datatype 'a listview = NIL | CONS of 'a * 'a seq
  datatype 'a treeview = EMPTY | ELT of 'a | NODE of 'a seq * 'a seq

  exception Range
  exception Size

  fun nth s i = List.nth (s, i) handle Subscript => raise Range
  fun toList (x : 'a seq) : 'a list = x
  fun toString f s = "<" ^ String.concatWith "," (map f s) ^ ">"

  fun empty () = []
  fun singleton x = [x]
  fun tabulate f n = List.tabulate (n, f)
  fun fromList (x : 'a list) : 'a seq = x
  val % = fromList

  val append = op@
  val flatten = List.concat

  fun map2 f [] _ = []
    | map2 f _ [] = []
    | map2 f (x::xs) (y::ys) = f (x,y)::map2 f xs ys

  fun zip s1 s2 = map2 (fn x => x) s1 s2

  fun equal eq (s1, s2) =
      length s1 = length s2 andalso List.all eq (zip s1 s2)

  fun enum s =
      let
        fun addIdx (_, []) = []
          | addIdx (i, x::xs) = (i,x)::addIdx (i+1, xs)
      in addIdx (0, s)
      end

  fun filterIdx p = map (fn (_,x) => x) o (filter p) o enum
  fun mapIdx f = (map f) o enum

  fun subseq _ (0, 0) = []
    | subseq [] (0, _) = raise Size
    | subseq [] _ = raise Range
    | subseq (x::xs) (i, len) =
      case Int.compare (i, 0)
        of EQUAL => x::subseq xs (0, len-1)
         | LESS => raise Range
         | GREATER => subseq xs (i-1, len)

  fun showl [] = NIL
    | showl (x::xs) = CONS (x, xs)

  fun showt [] = EMPTY
    | showt [x] = ELT x
    | showt s =
      let val half = length s div 2
      in NODE (take (s, half), drop (s, half))
      end

  fun inject [] s = s
    | inject ((i, x')::ixs) s =
      if i < 0 then raise Range
      else let
        fun update ([], _) = raise Range
          | update (x::xs, 0) = x'::xs
          | update (x::xs, n) = x::update (xs, n-1)
      in inject ixs (update (s, i))
      end

  fun iter f b = List.foldl (fn (x,b) => f (b,x)) b

  fun iterh f b [] = ([], b)
    | iterh f b (x::xs) =
      let
        val y = f (b, x)
        val (ys, r) = iterh f y xs
      in (y::ys, r)
      end

  fun reduce f b s =
      case length s
        of 0 => b
         | n => let
                  fun pp2 x n = if n >= x then n div 2 else pp2 x (2*n)
                  fun prevPow2 x = pp2 x 1
                  fun reduce' s =
                      case length s
                        of 1 => nth s 0
                         | n => let val half = prevPow2 n
                                in f (reduce' (take (s, half)),
                                      reduce' (drop (s, half)))
                                end
                in f (b, reduce' s)
                end

  fun scan _ b [] = ([], b)
    | scan f b [x] = ([b], f (b, x))
    | scan f b s =
      let
        exception Mismatch
        fun contract [] = []
          | contract [x] = [x]
          | contract (x::y::z) = f (x, y)::contract z
        val (rs, result) = scan f b (contract s)
        fun expand ([], []) = []
          | expand ([r], [_]) = [r]
          | expand (r::rs, x::_::xs) =
            r::f (r, x)::expand (rs, xs)
          | expand _ = raise Mismatch
      in (expand (rs, s), result)
      end

  fun scani f b s =
      let val (r, res) = scan f b s
      in drop (append (r, singleton res), 1)
      end

  fun merge _ [] _ = []
    | merge _ _ [] = []
    | merge cmp (x::xs) (y::ys) =
      if cmp (y, x) = LESS
      then y::merge cmp (x::xs) ys
      else x::merge cmp xs (y::ys)

  fun sort cmp =
      let
        fun partition _ [] k = k ([], [], [])
          | partition x (x'::xs) k =
            partition x xs (fn (l,e,g) =>
              case cmp (x', x)
                of LESS => k (x'::l,e,g)
                 | EQUAL => k (l,x'::e,g)
                 | GREATER => k (l,e,x'::g))

        fun qs [] = []
          | qs [x] = [x]
          | qs (x::xs) =
            let val (l,e,g) = partition x xs (fn x => x)
            in qs l @ x::e @ qs g
            end
      in qs
      end

  fun unmap2 spl [] = ([], [])
    | unmap2 spl (p::ps) =
      let val (x, y) = spl p
          val (xs, ys) = unmap2 spl ps
      in (x::xs, y::ys)
      end

  fun unzip s = unmap2 (fn x => x) s

  fun collect cmp s =
      let
        fun gather k vs [] = ((k,vs), [])
          | gather k vs ((k',v)::rest) =
            if cmp (k,k') <> EQUAL then ((k,vs), (k',v)::rest)
            else gather k (v::vs) rest

        fun partition [] = []
          | partition ((k,v)::rest) =
            let val ((k, vs), rest') = gather k [v] rest
            in (k, rev vs)::partition rest'
            end
      in partition (sort (fn ((x,_), (y,_)) => cmp (x,y)) s)
      end

  fun collate _ ([], []) = EQUAL
    | collate _ (nil, _) = LESS
    | collate _ (_, nil) = GREATER
    | collate cmp (x::xs, y::ys) =
      case cmp (x, y)
        of EQUAL => collate cmp (xs, ys)
         | ord => ord

  fun argmax _ [] = raise Range
    | argmax cmp (x::xs) =
      let
        fun best ((i, x), (mi, mx)) =
            if cmp (x, mx) = GREATER then (i, x) else (mi, mx)
        val (idx, _) = List.foldl best (0, x) (enum (x::xs))
      in idx
      end
end
