open! Base

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
module Brother_tree_set = Brother_tree.Set.Make (T)
module Brother_tree_map = Brother_tree.Map.Make (T)
include Core.Comparable.Make (T)
include Core.Hashable.Make (T)
