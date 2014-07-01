structure Primitives : PRIMITIVES =
struct
  (* Parallelism can't ordinarily be expressed in SML, so we introduce these
   * these "magical" primitive functions that we consider to run in parallel.
   * Do not rely on the implementations of these functions being sequential.
   * The construction "(f (), g (), ...)" is NOT considered to be parallel. *)
  fun par (f, g) = (f (), g ())
  fun par3 (f, g, h) =  (f (), g (), h ())
  fun parTab (n, f) = let val v = Vector.tabulate (n, f)
                      in fn i => Vector.sub (v, i) end
end
