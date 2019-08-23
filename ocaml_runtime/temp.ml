open! Core

module T = struct
  type t = string * int [@@deriving sexp]

  let counter = ref 0

  let create s = (s, (counter := !counter + 1; !counter))

  let hash (_, id) = Int.hash id

  let hash_fold_t state (_, id) = Int.hash_fold_t state id

  let compare (_, id1) (_, id2) = Int.compare id1 id2

  let name (s, _) = s
end

include T
include Comparable.Make (T)
include Hashable.Make (T)
