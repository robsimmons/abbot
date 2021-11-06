open! Base

module type S = sig
  type t [@@deriving compare, equal, hash, sexp]

  module Brother_tree_set : Brother_tree.Set.Specialized with type elt = t
  module Brother_tree_map : Brother_tree.Map.Specialized
    with type key = t
    with type set = Brother_tree_set.t
    with type non_empty_set = Brother_tree_set.Non_empty.t

  (* CR wduff: Eventually fully get rid of comparable in exchange for Brother_tree stuff. *)
  include Core.Comparable.S with type t := t
  include Core.Hashable.S with type t := t

  (* Creates a new, globally unique temp. *)
  val create : string -> t

  (* Provides the string used to create the temp. *)
  val name : t -> string
end
