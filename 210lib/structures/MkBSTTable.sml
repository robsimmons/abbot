(**
 * 210lib/MkBSTTable.sml
 *
 * Implements TABLE and SET simultaneously where
 *   type 'a table = 'a bst and
 *   type set = unit bst
 * The key type is defined in the argument structure Tree.Key.
 *)
functor MkBSTTable(structure Tree : BSTREE
                   structure Seq : SEQUENCE) : TABLE =
struct
  (* The substructure BSTTbl contains functions shared between
   * the TABLE and SET implementations.
   *)
  structure BSTTbl =
  struct
    structure Seq = Seq
    open Tree

    type 'a seq = 'a Seq.seq
    type key = Key.t

    fun iter f b t =
        case expose t
          of NONE => b
           | SOME {key, value, left, right} =>
             iter f (f (iter f b left, (key, value))) right

    fun iterh f b =
        let
          fun itr state t =
              case expose t
                of NONE => (empty (), state)
                 | SOME {key=k, value=v, left=l, right=r} =>
                   let
                     val (tL, sL) = itr state l
                     val state' = f (sL, (k,v))
                     val (tR, sR) = itr state' r
                   in (makeNode {key=k, value=sL, left=tL, right=tR}, sR)
                   end
        in itr b
        end

    (* sequential is probably the best bet since Seq is abstract *)
    fun toSeq t = Seq.fromList (iter (fn (l, kv) => kv::l) [] t)

    fun toString f t =
        "{" ^ String.concatWith "," (Seq.toList (Seq.map f (toSeq t))) ^ "}"

    fun find t k =
        case expose t
          of NONE => NONE
           | SOME {key, value, left, right} =>
             case Key.compare (k, key)
               of EQUAL => SOME value
                | LESS => find left k
                | GREATER => find right k

    fun mapfilter p t =
        case expose t
          of NONE => empty ()
           | SOME {key=k, value=v, left=l, right=r} =>
             let val (l', r', vOpt) =
               Primitives.par3 (fn () => mapfilter p l,
                                fn () => mapfilter p r,
                                fn () => p (k, v))
             in case vOpt
                  of SOME v' => makeNode {key=k, value=v', left=l', right=r'}
                   | NONE => join (l', r')
             end

    fun filterk p = mapfilter (fn (k,v) => if p (k,v) then SOME v else NONE)

    (* combine takes a function (f : 'a option * 'b option -> 'c option)
     * and for every k, if (f (find t1 k, find t2 k) ==> SOME v') then
     * the resulting 'c bst will contain the mapping k -> v'.
     *)
    fun combine f (t1, t2) =
        case expose t1
          of NONE => mapfilter (fn (_,v) => f (NONE, SOME v)) t2
           | SOME {key=k1, value=v1, left=l1, right=r1} =>
             let
               val (l2, v2Opt, r2) = splitAt (t2, k1)
               val (l, r, vOpt) =
                 Primitives.par3 (fn () => combine f (l1, l2),
                                  fn () => combine f (r1, r2),
                                  fn () => f (SOME v1, v2Opt))
             in case vOpt
                  of NONE => join (l, r)
                   | SOME v => makeNode {key=k1, value=v, left=l, right=r}
             end

    fun merge f =
        combine (fn ((vOpt, NONE) | (NONE, vOpt)) => vOpt
                  | (SOME v1, SOME v2) => SOME (f (v1, v2)))

    fun extract (t1, t2) =
        combine (fn (_, NONE) => NONE
                  | (vOpt, SOME ()) => vOpt) (t1, t2)

    fun erase (t1, t2) =
        combine (fn (vOpt, NONE) => vOpt
                  | (_, SOME ()) => NONE) (t1, t2)

    val $ = singleton
    fun insert f kv t = merge f (t, singleton kv)

    fun delete k t =
        let val (l, _, r) = splitAt (t, k)
        in join (l, r)
        end

    fun fromSeq s =
        Seq.reduce (merge (fn (x,_) => x)) (empty ()) (Seq.map singleton s)
  end

  structure Set =
  struct
    open BSTTbl
    type set = unit bst

    fun toString S = BSTTbl.toString (fn (k,_) => Key.toString k) S
    fun toSeq S = Seq.map (fn (a,_) => a) (BSTTbl.toSeq S)
    fun singleton k = BSTTbl.singleton (k, ())
    fun fromSeq S = BSTTbl.fromSeq (Seq.map (fn a => (a,())) S)

    fun find S k = isSome (BSTTbl.find S k)
    fun insert k = BSTTbl.insert (fn _ => ()) (k, ())
    fun filter p = BSTTbl.filterk (fn (k, _) => p k)

    val union = merge (fn _ => ())
    val intersection = extract
    val difference = erase

    type t = set
    fun $ k = BSTTbl.$ (k, ())
  end

  open BSTTbl

  type 'a table = 'a bst
  type set = Set.t

  fun mapk f = mapfilter (SOME o f)
  fun map f = mapk (fn (_, v) => f v)
  fun filter p = filterk (fn (_,v) => p v)
  fun tabulate f S = mapk (fn (k, _) => f k) S
  fun domain t = map (fn v => ()) t
  fun range t = Seq.map (fn (k, v) => v) (toSeq t)
  fun collect S = fromSeq (Seq.collect Key.compare S)

  fun reduce f b t =
      Seq.reduce f b (range t)

  fun toString f =
      BSTTbl.toString (fn (k,v) => "(" ^ Key.toString k ^ "->" ^ f v ^ ")")

end
