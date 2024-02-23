open! Base

module type Abstract_non_empty_tree = sig
  type 'a t [@@deriving sexp_of]

  val length : _ t -> int

  val singleton : 'a -> 'a t

  val of_array : 'a array -> 'a t
  val of_list : 'a list -> 'a t

  val to_list : 'a t -> 'a list

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val iter : 'a t -> f:('a -> unit) -> unit
  val fold : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold_right : 'a t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold_map : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t

  val find_leftmost : 'a t -> 'a
  val find_rightmost : 'a t -> 'a
end

module type Abstract_tree = sig
  module Non_empty : Abstract_non_empty_tree

  type 'a t [@@deriving sexp_of]

  val length : _ t -> int

  val empty : _ t
  val is_empty : _ t -> bool

  val singleton : 'a -> 'a t

  val of_non_empty : 'a Non_empty.t -> 'a t
  val of_non_empty_option : 'a Non_empty.t option -> 'a t
  val get_non_empty : 'a t -> 'a Non_empty.t option
  val get_non_empty_exn : 'a t -> 'a Non_empty.t

  val of_array : 'a array -> 'a t
  val of_list : 'a list -> 'a t

  val to_list : 'a t -> 'a list

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val iter : 'a t -> f:('a -> unit) -> unit
  val fold : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold_right : 'a t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold_map : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t

  val find_leftmost : 'a t -> 'a option
  val find_leftmost_exn : 'a t -> 'a

  val find_rightmost : 'a t -> 'a option
  val find_rightmost_exn : 'a t -> 'a
end

module type Non_empty_tree = sig
  type 'a t =
    | Leaf1 of 'a
    | Leaf2 of 'a * 'a
    | Two of 'a t * 'a  * 'a t
    | OneTwo of 'a t * 'a  * 'a t
    | TwoOne of 'a t * 'a  * 'a t

  include Abstract_non_empty_tree with type 'a t := 'a t
end

module type Tree = sig
  module Non_empty : Non_empty_tree

  type 'a t = 'a Non_empty.t option

  include Abstract_tree with type 'a t := 'a t with module Non_empty := Non_empty
end

(* CR wduff: Move these out of the intf file. *)
module Height_increase : sig
  type t =
    | Height_unchanged
    | Height_increased

  (* [to_int] is like [function Height_unchanged -> 0 | Height_increased -> 1], but without the
     conditional branch. *)
  val to_int : t -> int
end = struct
  type t =
    | Height_unchanged
    | Height_increased

  let to_int (t : t) = (Stdlib.Obj.magic t : int)
end

module Height_decrease : sig
  type t =
    | Height_unchanged
    | Height_decreased

  (* [to_int] is like [function Height_unchanged -> 0 | Height_decreased -> 1], but without the
     conditional branch. *)
  val to_int : t -> int
end = struct
  type t =
    | Height_unchanged
    | Height_decreased

  let to_int (t : t) = (Stdlib.Obj.magic t : int)
end

module type Non_empty_balanced_tree = sig
  type 'a raw_tree
  type 'a maybe_empty

  include Abstract_non_empty_tree

  val height : _ t -> int

  val of_raw_tree : 'a raw_tree -> 'a t
  val of_balanced_raw_tree_unchecked : 'a raw_tree -> 'a t
  val of_balanced_raw_tree_exn : 'a raw_tree -> 'a t
  val to_raw_tree : 'a t -> 'a raw_tree

  val remove_leftmost : 'a t -> 'a maybe_empty
  val remove_leftmost' : 'a t -> ('a t * Height_decrease.t) option
  val find_and_remove_leftmost : 'a t -> 'a * 'a maybe_empty
  val find_and_remove_leftmost' : 'a t -> 'a * ('a t * Height_decrease.t) option

  val remove_rightmost : 'a t -> 'a maybe_empty
  val remove_rightmost' : 'a t -> ('a t * Height_decrease.t) option
  val find_and_remove_rightmost : 'a t -> 'a * 'a maybe_empty
  val find_and_remove_rightmost' : 'a t -> 'a * ('a t * Height_decrease.t) option

  (* CR wduff: These are kinda raw interfaces to be exposing here. In whatever form we keep them, we
     need them in the maybe_empty case as well. *)
  val join_into_left : 'a t -> 'a -> 'a t -> height_difference:int -> 'a t * Height_increase.t
  val join_into_right : 'a t -> 'a -> 'a t -> height_difference:int -> 'a t * Height_increase.t
  val join : 'a t -> int -> 'a -> 'a t -> int -> 'a t * int
  val join0 : 'a t -> int -> 'a t -> int -> 'a t * int
end

module type Balanced_tree = sig
  type 'a raw_tree
  type 'a non_empty_raw_tree
  type 'a t

  module Non_empty
    : Non_empty_balanced_tree
      with type 'a raw_tree := 'a non_empty_raw_tree
      with type 'a maybe_empty := 'a t

  include Abstract_tree with type 'a t := 'a t with module Non_empty := Non_empty

  val height : _ t -> int

  val of_raw_tree : 'a raw_tree -> 'a t
  val of_balanced_raw_tree_unchecked : 'a raw_tree -> 'a t
  val of_balanced_raw_tree_exn : 'a raw_tree -> 'a t
  val to_raw_tree : 'a t -> 'a raw_tree

  val remove_leftmost : 'a t -> 'a t
  val remove_leftmost' : 'a t -> 'a t * Height_decrease.t
  val find_and_remove_leftmost : 'a t -> 'a option * 'a t
  val find_and_remove_leftmost' : 'a t -> 'a option * 'a t * Height_decrease.t

  val remove_rightmost : 'a t -> 'a t
  val remove_rightmost' : 'a t -> 'a t * Height_decrease.t
  val find_and_remove_rightmost : 'a t -> 'a option * 'a t
  val find_and_remove_rightmost' : 'a t -> 'a option * 'a t * Height_decrease.t
end

module type Abstract_non_empty_tree2 = sig
  type 'a tree1

  type ('a, 'b) t [@@deriving sexp_of]

  val length : _ t -> int

  val singleton : 'a -> 'b -> ('a, 'b) t

  val of_array : ('a * 'b) array -> ('a, 'b) t
  val of_list : ('a * 'b) list -> ('a, 'b) t

  val to_pair_list : ('a, 'b) t -> ('a * 'b) list
  val to_list1 : ('a, 'b) t -> 'a list
  val to_list2 : ('a, 'b) t -> 'b list

  val to_pair_tree : ('a, 'b) t -> ('a * 'b) tree1
  val to_tree1 : ('a, 'b) t -> 'a tree1
  val to_tree2 : ('a, 'b) t -> 'b tree1

  val map_both : ('a1, 'b1) t -> f:('a1 -> 'b1 -> 'a2 * 'b2) -> ('a2, 'b2) t
  val map1 : ('a1, 'b) t -> f:('a1 -> 'a2) -> ('a2, 'b) t
  val map2 : ('a, 'b1) t -> f:('b1 -> 'b2) -> ('a, 'b2) t

  val iter_both : ('a, 'b) t -> f:('a -> 'b -> unit) -> unit
  val iter1 : ('a, 'b) t -> f:('a -> unit) -> unit
  val iter2 : ('a, 'b) t -> f:('b -> unit) -> unit

  val fold_both : ('a, 'b) t -> init:'acc -> f:('acc -> 'a -> 'b -> 'acc) -> 'acc
  val fold1 : ('a, 'b) t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold2 : ('a, 'b) t -> init:'acc -> f:('acc -> 'b -> 'acc) -> 'acc

  val fold_both_right : ('a, 'b) t -> init:'acc -> f:('a -> 'b -> 'acc -> 'acc) -> 'acc
  val fold1_right : ('a, 'b) t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold2_right : ('a, 'b) t -> init:'acc -> f:('b -> 'acc -> 'acc) -> 'acc

  val fold_map_both
    : ('a1, 'b1) t -> init:'acc -> f:('acc -> 'a1 -> 'b1 -> 'acc * 'a2 * 'b2) -> 'acc * ('a2, 'b2) t
  val fold_map1 : ('a1, 'b) t -> init:'acc -> f:('acc -> 'a1 -> 'acc * 'a2) -> 'acc * ('a2, 'b) t
  val fold_map2 : ('a, 'b1) t -> init:'acc -> f:('acc -> 'b1 -> 'acc * 'b2) -> 'acc * ('a, 'b2) t

  val find_leftmost : ('a, 'b) t -> 'a * 'b
  val find_rightmost : ('a, 'b) t -> 'a * 'b
end

module type Abstract_tree2 = sig
  type 'a tree1
  type 'a non_empty_tree1

  module Non_empty : Abstract_non_empty_tree2 with type 'a tree1 := 'a non_empty_tree1

  type ('a, 'b) t [@@deriving sexp_of]

  val length : _ t -> int

  val empty : _ t
  val is_empty : _ t -> bool

  val singleton : 'a -> 'b -> ('a, 'b) t

  val of_non_empty : ('a, 'b) Non_empty.t -> ('a, 'b) t
  val of_non_empty_option : ('a, 'b) Non_empty.t option -> ('a, 'b) t
  val get_non_empty : ('a, 'b) t -> ('a, 'b) Non_empty.t option
  val get_non_empty_exn : ('a, 'b) t -> ('a, 'b) Non_empty.t

  val of_array : ('a * 'b) array -> ('a, 'b) t
  val of_list : ('a * 'b) list -> ('a, 'b) t

  val to_pair_list : ('a, 'b) t -> ('a * 'b) list
  val to_list1 : ('a, 'b) t -> 'a list
  val to_list2 : ('a, 'b) t -> 'b list

  val to_pair_tree : ('a, 'b) t -> ('a * 'b) tree1
  val to_tree1 : ('a, 'b) t -> 'a tree1
  val to_tree2 : ('a, 'b) t -> 'b tree1

  val map_both : ('a1, 'b1) t -> f:('a1 -> 'b1 -> 'a2 * 'b2) -> ('a2, 'b2) t
  val map1 : ('a1, 'b) t -> f:('a1 -> 'a2) -> ('a2, 'b) t
  val map2 : ('a, 'b1) t -> f:('b1 -> 'b2) -> ('a, 'b2) t

  val iter_both : ('a, 'b) t -> f:('a -> 'b -> unit) -> unit
  val iter1 : ('a, 'b) t -> f:('a -> unit) -> unit
  val iter2 : ('a, 'b) t -> f:('b -> unit) -> unit

  val fold_both : ('a, 'b) t -> init:'acc -> f:('acc -> 'a -> 'b -> 'acc) -> 'acc
  val fold1 : ('a, 'b) t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold2 : ('a, 'b) t -> init:'acc -> f:('acc -> 'b -> 'acc) -> 'acc

  val fold_both_right : ('a, 'b) t -> init:'acc -> f:('a -> 'b -> 'acc -> 'acc) -> 'acc
  val fold1_right : ('a, 'b) t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold2_right : ('a, 'b) t -> init:'acc -> f:('b -> 'acc -> 'acc) -> 'acc

  val fold_map_both
    : ('a1, 'b1) t -> init:'acc -> f:('acc -> 'a1 -> 'b1 -> 'acc * 'a2 * 'b2) -> 'acc * ('a2, 'b2) t
  val fold_map1 : ('a1, 'b) t -> init:'acc -> f:('acc -> 'a1 -> 'acc * 'a2) -> 'acc * ('a2, 'b) t
  val fold_map2 : ('a, 'b1) t -> init:'acc -> f:('acc -> 'b1 -> 'acc * 'b2) -> 'acc * ('a, 'b2) t

  val find_leftmost : ('a, 'b) t -> ('a * 'b) option
  val find_leftmost_exn : ('a, 'b) t -> 'a * 'b

  val find_rightmost : ('a, 'b) t -> ('a * 'b) option
  val find_rightmost_exn : ('a, 'b) t -> 'a * 'b
end

module type Non_empty_tree2 = sig
    type ('a, 'b) t =
      | Leaf1 of 'a * 'b
      | Leaf2 of 'a * 'b * 'a * 'b
      | Two of ('a, 'b) t * 'a * 'b * ('a, 'b) t
      | OneTwo of ('a, 'b) t * 'a * 'b * ('a, 'b) t
      | TwoOne of ('a, 'b) t * 'a * 'b * ('a, 'b) t

  include Abstract_non_empty_tree2 with type ('a, 'b) t := ('a, 'b) t
end

module type Tree2 = sig
  type 'a tree1
  type 'a non_empty_tree1

  module Non_empty : Non_empty_tree2 with type 'a tree1 := 'a non_empty_tree1

  type ('a, 'b) t = ('a, 'b) Non_empty.t option

  include Abstract_tree2
    with type 'a tree1 := 'a tree1
    with type 'a non_empty_tree1 := 'a non_empty_tree1
    with type ('a, 'b) t := ('a, 'b) t with module Non_empty := Non_empty
end

module type Non_empty_balanced_tree2 = sig
  type ('a, 'b) raw_tree
  type ('a, 'b) maybe_empty

  include Abstract_non_empty_tree2

  val height : _ t -> int

  val of_raw_tree : ('a, 'b) raw_tree -> ('a, 'b) t
  val of_balanced_raw_tree_unchecked : ('a, 'b) raw_tree -> ('a, 'b) t
  val of_balanced_raw_tree_exn : ('a, 'b) raw_tree -> ('a, 'b) t
  val to_raw_tree : ('a, 'b) t -> ('a, 'b) raw_tree

  val remove_leftmost : ('a, 'b) t -> ('a, 'b) maybe_empty
  val remove_leftmost' : ('a, 'b) t -> (('a, 'b) t * Height_decrease.t) option
  val find_and_remove_leftmost : ('a, 'b) t -> ('a * 'b) * ('a, 'b) maybe_empty
  val find_and_remove_leftmost' : ('a, 'b) t -> ('a * 'b) * (('a, 'b) t * Height_decrease.t) option

  val remove_rightmost : ('a, 'b) t -> ('a, 'b) maybe_empty
  val remove_rightmost' : ('a, 'b) t -> (('a, 'b) t * Height_decrease.t) option
  val find_and_remove_rightmost : ('a, 'b) t -> ('a * 'b) * ('a, 'b) maybe_empty
  val find_and_remove_rightmost' : ('a, 'b) t -> ('a * 'b) * (('a, 'b) t * Height_decrease.t) option

  (* CR wduff: These are kinda raw interfaces to be exposing here. In whatever form we keep them, we
     need them in the maybe_empty case as well. *)
  val join_into_left
    : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t -> height_difference:int -> ('a, 'b) t * Height_increase.t
  val join_into_right
    : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t -> height_difference:int -> ('a, 'b) t * Height_increase.t
  val join : ('a, 'b) t -> int -> 'a -> 'b -> ('a, 'b) t -> int -> ('a, 'b) t * int
  val join0 : ('a, 'b) t -> int -> ('a, 'b) t -> int -> ('a, 'b) t * int
end

module type Balanced_tree2 = sig
  type 'a tree1
  type 'a non_empty_tree1
  type ('a, 'b) raw_tree
  type ('a, 'b) non_empty_raw_tree
  type ('a, 'b) t

  module Non_empty
    : Non_empty_balanced_tree2
      with type 'a tree1 := 'a non_empty_tree1
      with type ('a, 'b) raw_tree := ('a, 'b) non_empty_raw_tree
      with type ('a, 'b) maybe_empty := ('a, 'b) t

  include Abstract_tree2
    with type 'a tree1 := 'a tree1
    with type 'a non_empty_tree1 := 'a non_empty_tree1
    with type ('a, 'b) t := ('a, 'b) t with module Non_empty := Non_empty

  val height : _ t -> int

  val of_raw_tree : ('a, 'b) raw_tree -> ('a, 'b) t
  val of_balanced_raw_tree_unchecked : ('a, 'b) raw_tree -> ('a, 'b) t
  val of_balanced_raw_tree_exn : ('a, 'b) raw_tree -> ('a, 'b) t
  val to_raw_tree : ('a, 'b) t -> ('a, 'b) raw_tree

  val remove_leftmost : ('a, 'b) t -> ('a, 'b) t
  val find_and_remove_leftmost : ('a, 'b) t -> ('a * 'b) option * ('a, 'b) t

  val remove_rightmost : ('a, 'b) t -> ('a, 'b) t
  val find_and_remove_rightmost : ('a, 'b) t -> ('a * 'b) option * ('a, 'b) t
end

module type Comparable = sig
  type t [@@deriving compare, sexp_of]
end

module Compare : sig
  type ('a, 'witness) t = private ('a -> 'a -> int)

  module Make (Comparable : Comparable) : sig
    type compare_witness

    val compare : (Comparable.t, compare_witness) t
  end

  module Packed : sig
    type ('a, 'witness) unpacked := ('a, 'witness) t
    type 'a t = T : ('a, _) unpacked -> 'a t
  end

  val create : ('a -> 'a -> int) -> 'a Packed.t
  val convert : ('a, _) t -> ('a -> 'a -> int)
  val do_compare : ('a, _) t -> 'a -> 'a -> Ordering.t
end = struct
  type ('a, 'witness) t = 'a -> 'a -> int

  module Make (Comparable : Comparable) = struct
    type compare_witness

    let compare = Comparable.compare
  end

  module Packed = struct
    type ('a, 'witness) unpacked = ('a, 'witness) t
    type 'a t = T : ('a, _) unpacked -> 'a t
  end

  let create compare : 'a Packed.t = T compare
  let convert (compare : ('a, 'witness) t) = (compare :> 'a -> 'a -> int)
  let do_compare compare x y = Ordering.of_int (convert compare x y)
end

type ('a, 'witness) compare = ('a, 'witness) Compare.t

module type Non_empty_set = sig
  type 'a balanced_tree
  type ('a, 'cmp) maybe_empty

  type ('a, 'cmp) t [@@deriving sexp_of]

  val height : _ t -> int
  val length : _ t -> int

  val singleton : 'a -> ('a, _) t

  val to_list : ('a, _) t -> 'a list

  val iter : ('a, _) t -> f:('a -> unit) -> unit
  val fold : ('a, _) t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold_right : ('a, _) t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc

  val of_array : 'a array -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val of_sorted_array_unchecked : 'a array -> ('a, _) t
  val of_sorted_array_exn : 'a array -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val of_list : 'a list -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val of_sorted_list_unchecked : 'a list -> ('a, _) t
  val of_sorted_list_exn : 'a list -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val of_sorted_balanced_tree_unchecked : 'a balanced_tree -> ('a, _) t
  val of_sorted_balanced_tree_exn : 'a balanced_tree -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val to_balanced_tree : ('a, 'cmp) t -> 'a balanced_tree

  val resorting_map : ('a, _) t -> f:('a -> 'b) -> compare:('b, 'cmp) compare -> ('b, 'cmp) t

  val mem : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> bool

  val add : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val strict_add : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> [ `Ok of ('a, 'cmp) t | `Duplicate_elt ]
  val strict_add_exn : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val generic_add
    :  ('a, 'cmp) t
    -> 'a
    -> on_already_present:('a -> unit)
    -> compare:('a, 'cmp) compare
    -> ('a, 'cmp) t

  val union : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val remove : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) maybe_empty
  val strict_remove : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> [ `Ok of ('a, 'cmp) maybe_empty | `Not_found ]
  val strict_remove_exn : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) maybe_empty

  val inter : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) maybe_empty
  val xor : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) maybe_empty
  val diff : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) maybe_empty

  val find_min : ('a, _) t -> 'a
  val remove_min : ('a, 'cmp) t -> ('a, 'cmp) maybe_empty
  val find_and_remove_min : ('a, 'cmp) t -> 'a * ('a, 'cmp) maybe_empty

  val find_max : ('a, _) t -> 'a
  val remove_max : ('a, 'cmp) t -> ('a, 'cmp) maybe_empty
  val find_and_remove_max : ('a, 'cmp) t -> 'a * ('a, 'cmp) maybe_empty
end

module type Set = sig
  type 'a balanced_tree
  type 'a non_empty_balanced_tree
  type ('a, 'cmp) t [@@deriving sexp_of]

  val height : _ t -> int
  val length : _ t -> int

  val singleton : 'a -> ('a, _) t

  val to_list : ('a, _) t -> 'a list

  val iter : ('a, _) t -> f:('a -> unit) -> unit
  val fold : ('a, _) t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold_right : ('a, _) t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc

  val of_array : 'a array -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val of_sorted_array_unchecked : 'a array -> ('a, _) t
  val of_sorted_array_exn : 'a array -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val of_list : 'a list -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val of_sorted_list_unchecked : 'a list -> ('a, _) t
  val of_sorted_list_exn : 'a list -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val of_sorted_balanced_tree_unchecked : 'a balanced_tree -> ('a, _) t
  val of_sorted_balanced_tree_exn : 'a balanced_tree -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val to_balanced_tree : ('a, 'cmp) t -> 'a balanced_tree

  val resorting_map : ('a, _) t -> f:('a -> 'b) -> compare:('b, 'cmp) compare -> ('b, 'cmp) t

  val mem : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> bool

  val add : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val strict_add : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> [ `Ok of ('a, 'cmp) t | `Duplicate_elt ]
  val strict_add_exn : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val generic_add
    :  ('a, 'cmp) t
    -> 'a
    -> on_already_present:('a -> unit)
    -> compare:('a, 'cmp) compare
    -> ('a, 'cmp) t

  val union : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  module Non_empty
    : Non_empty_set
      with type 'a balanced_tree := 'a non_empty_balanced_tree
      with type ('a, 'cmp) maybe_empty := ('a, 'cmp) t

  val empty : _ t

  val is_empty : _ t -> bool

  val of_non_empty : ('a, 'cmp) Non_empty.t -> ('a, 'cmp) t
  val of_non_empty_option : ('a, 'cmp) Non_empty.t option -> ('a, 'cmp) t
  val get_non_empty : ('a, 'cmp) t -> ('a, 'cmp) Non_empty.t option
  val get_non_empty_exn : ('a, 'cmp) t -> ('a, 'cmp) Non_empty.t

  val add_non_empty : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) Non_empty.t
  val strict_add_non_empty
    : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> [ `Ok of ('a, 'cmp) Non_empty.t | `Duplicate_elt ]
  val strict_add_non_empty_exn : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) Non_empty.t
  val generic_add_non_empty
    : ('a, 'cmp) t -> 'a -> on_already_present:('a -> unit) -> compare:('a, 'cmp) compare -> ('a, 'cmp) Non_empty.t

  val remove : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val strict_remove : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> [ `Ok of ('a, 'cmp) t | `Not_found ]
  val strict_remove_exn : ('a, 'cmp) t -> 'a -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val inter : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val xor : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) t
  val diff : ('a, 'cmp) t -> ('a, 'cmp) t -> compare:('a, 'cmp) compare -> ('a, 'cmp) t

  val find_min : ('a, _) t -> 'a option
  val find_min_exn : ('a, _) t -> 'a
  val remove_min : ('a, 'cmp) t -> ('a, 'cmp) t
  val find_and_remove_min : ('a, 'cmp) t -> 'a option * ('a, 'cmp) t

  val find_max : ('a, _) t -> 'a option
  val find_max_exn : ('a, _) t -> 'a
  val remove_max : ('a, 'cmp) t -> ('a, 'cmp) t
  val find_and_remove_max : ('a, 'cmp) t -> 'a option * ('a, 'cmp) t
end

module type Non_empty_map = sig
  type ('a, 'cmp) set
  type ('a, 'b) balanced_tree
  type ('k, 'v, 'cmp) maybe_empty

  type ('k, 'v, 'cmp) t [@@deriving sexp_of]

  val height : _ t -> int
  val length : _ t -> int

  val singleton : key:'k -> data:'v -> ('k, 'v, 'cmp) t

  val of_array : ('k * 'v) array -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val of_sorted_array_unchecked : ('k * 'v) array -> ('k, 'v, _) t
  val of_sorted_array_exn : ('k * 'v) array -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val of_list : ('k * 'v) list -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val of_sorted_list_unchecked : ('k * 'v) list -> ('k, 'v, _) t
  val of_sorted_list_exn : ('k * 'v) list -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val of_sorted_balanced_tree_unchecked : ('k, 'v) balanced_tree -> ('k, 'v, _) t
  val of_sorted_balanced_tree_exn
    : ('k, 'v) balanced_tree -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val to_balanced_tree : ('k, 'v, 'cmp) t -> ('k, 'v) balanced_tree

  val to_list : ('k, 'v, _) t -> ('k * 'v) list
  val keys : ('k, _, _) t -> 'k list
  val key_set : ('k, _, 'cmp) t -> ('k, 'cmp) set
  val data : (_, 'v, _) t -> 'v list

  val map : ('k, 'v1, 'cmp) t -> f:('v1 -> 'v2) -> ('k, 'v2, 'cmp) t
  val iter : (_, 'v, _) t -> f:('v -> unit) -> unit
  val iteri : ('k, 'v, _) t -> f:(key:'k -> data:'v -> unit) -> unit
  val fold : (_, 'v, _) t -> init:'acc -> f:('acc -> 'v -> 'acc) -> 'acc
  val foldi : ('k, 'v, _) t -> init:'acc -> f:('acc -> key:'k -> data:'v -> 'acc) -> 'acc
  val fold_right : (_, 'v, _) t -> init:'acc -> f:('v -> 'acc -> 'acc) -> 'acc
  val fold_righti : ('k, 'v, _) t -> init:'acc -> f:(key:'k -> data:'v -> 'acc -> 'acc) -> 'acc
  val fold_map
    : ('k, 'v1, 'cmp) t -> init:'acc -> f:('acc -> 'v1 -> 'acc * 'v2) -> 'acc * ('k, 'v2, 'cmp) t
  val fold_mapi
    :  ('k, 'v1, 'cmp) t
    -> init:'acc
    -> f:('acc -> key:'k -> data:'v1 -> 'acc * 'v2)
    -> 'acc * ('k, 'v2, 'cmp) t

  val rekeying_map
    :  ('k1, 'v1, 'cmp1) t
    -> f:(key:'k1 -> data:'v1 -> 'k2 * 'v2)
    -> compare:('k2, 'cmp) compare
    -> ('k2, 'v2, 'cmp2) t

  val find : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> 'v option
  val find_exn : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> 'v
  val mem : ('k, _, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> bool
  val find_and_call
    :  ('k, 'v, 'cmp) t
    -> 'k
    -> if_found:('v -> 'a)
    -> if_not_found:(unit -> 'a)
    -> compare:('k, 'cmp) compare
    -> 'a

  val add
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> compare:('k, 'cmp) compare
    -> [ `Ok of ('k, 'v, 'cmp) t | `Duplicate_key ]
  val add_exn
    : ('k, 'v, 'cmp) t -> key:'k -> data:'v -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val set
    : ('k, 'v, 'cmp) t -> key:'k -> data:'v -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val set'
    : ('k, 'v, 'cmp) t -> key:'k -> data:'v -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t * Height_increase.t
  val generic_add
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> on_already_present:(key:'k -> old_data:'v -> new_data:'v -> 'v)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) t

  val remove
    : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) maybe_empty
  val find_and_remove
    : ('k, 'v, 'cmp) t
    -> 'k
    -> compare:('k, 'cmp) compare
    -> ('v * ('k, 'v, 'cmp) maybe_empty) option

  (* CR wduff: These are kinda raw interfaces to be exposing here. In whatever form we keep them, we
     need them in the maybe_empty case as well. *)
  val join_into_left
    : ('k, 'v, 'cmp) t -> 'k -> 'v -> ('k, 'v, 'cmp) t -> height_difference:int -> ('k, 'v, 'cmp) t * Height_increase.t
  val join_into_right
    : ('k, 'v, 'cmp) t -> 'k -> 'v -> ('k, 'v, 'cmp) t -> height_difference:int -> ('k, 'v, 'cmp) t * Height_increase.t
  val join : ('k, 'v, 'cmp) t -> int -> 'k -> 'v -> ('k, 'v, 'cmp) t -> int -> ('k, 'v, 'cmp) t * int
  val join0 : ('k, 'v, 'cmp) t -> int -> ('k, 'v, 'cmp) t -> int -> ('k, 'v, 'cmp) t * int

  (* CR wduff: Add this to all the other relevant interfaces. *)
  val split
    :  ('k, 'v, 'cmp) t
    -> 'k
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) maybe_empty * int * 'v option * ('k, 'v, 'cmp) maybe_empty * int

  val union
    :  ('k, 'v, 'cmp) t
    -> ('k, 'v, 'cmp) t
    -> merge:(key:'k -> 'v -> 'v -> 'v)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) t

  val inter
    :  ('k, 'v1, 'cmp) t
    -> ('k, 'v2, 'cmp) t
    -> merge:(key:'k -> 'v1 -> 'v2 -> 'v3)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v3, 'cmp) maybe_empty

  val xor
    :  ('k, 'v, 'cmp) t
    -> ('k, 'v, 'cmp) t
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) maybe_empty

  val remove_set
    :  ('k, 'v, 'cmp) t
    -> ('k, 'cmp) set
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) maybe_empty

  val restrict_to_set
    : ('k, 'v, 'cmp) t
    -> ('k, 'cmp) set
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) maybe_empty

  val filter_mapi
    : ('k, 'v1, 'cmp) t -> f:(key:'k -> data:'v1 -> 'v2 option) -> ('k, 'v2, 'cmp) maybe_empty

  val generic_merge
    :  ('k, 'v1, 'cmp) t
    -> ('k, 'v2, 'cmp) t
    -> merge:(key:'k -> [ `Left of 'v1 | `Right of 'v2 | `Both of 'v1 * 'v2 ] -> 'v3 option)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v3, 'cmp) maybe_empty

  val find_min : ('k, 'v, _) t -> 'k * 'v
  val remove_min : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) maybe_empty
  val find_and_remove_min : ('k, 'v, 'cmp) t -> ('k * 'v) * ('k, 'v, 'cmp) maybe_empty

  val find_max : ('k, 'v, _) t -> 'k * 'v
  val remove_max : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) maybe_empty
  val find_and_remove_max : ('k, 'v, 'cmp) t -> ('k * 'v) * ('k, 'v, 'cmp) maybe_empty
end

module type Map = sig
  type ('a, 'cmp) set
  type ('a, 'cmp) non_empty_set
  type ('a, 'b) balanced_tree
  type ('a, 'b) non_empty_balanced_tree

  type ('k, 'v, 'cmp) t [@@deriving sexp_of]

  module Non_empty
    : Non_empty_map
      with type ('a, 'cmp) set := ('a, 'cmp) non_empty_set
      with type ('a, 'b) balanced_tree := ('a, 'b) non_empty_balanced_tree
      with type ('k, 'v, 'cmp) maybe_empty := ('k, 'v, 'cmp) t

  val height : _ t -> int
  val length : _ t -> int

  val empty : _ t
  val is_empty : _ t -> bool

  val of_non_empty : ('k, 'v, 'cmp) Non_empty.t -> ('k, 'v, 'cmp) t
  val of_non_empty_option : ('k, 'v, 'cmp) Non_empty.t option -> ('k, 'v, 'cmp) t
  val get_non_empty : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) Non_empty.t option
  val get_non_empty_exn : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) Non_empty.t

  val singleton : key:'k -> data:'v -> ('k, 'v, _) t

  val of_array : ('k * 'v) array -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val of_sorted_array_unchecked : ('k * 'v) array -> ('k, 'v, _) t
  val of_sorted_array_exn : ('k * 'v) array -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val of_list : ('k * 'v) list -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val of_sorted_list_unchecked : ('k * 'v) list -> ('k, 'v, _) t
  val of_sorted_list_exn : ('k * 'v) list -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val of_sorted_balanced_tree_unchecked : ('k, 'v) balanced_tree -> ('k, 'v, _) t
  val of_sorted_balanced_tree_exn
    : ('k, 'v) balanced_tree -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val to_balanced_tree : ('k, 'v, 'cmp) t -> ('k, 'v) balanced_tree

  val to_list : ('k, 'v, _) t -> ('k * 'v) list
  val keys : ('k, _, _) t -> 'k list
  val key_set : ('k, _, 'cmp) t -> ('k, 'cmp) set
  val data : (_, 'v, _) t -> 'v list

  val map : ('k, 'v1, 'cmp) t -> f:('v1 -> 'v2) -> ('k, 'v2, 'cmp) t
  val iter : (_, 'v, _) t -> f:('v -> unit) -> unit
  val iteri : ('k, 'v, _) t -> f:(key:'k -> data:'v -> unit) -> unit
  val fold : (_, 'v, _) t -> init:'acc -> f:('acc -> 'v -> 'acc) -> 'acc
  val foldi : ('k, 'v, _) t -> init:'acc -> f:('acc -> key:'k -> data:'v -> 'acc) -> 'acc
  val fold_right : (_, 'v, _) t -> init:'acc -> f:('v -> 'acc -> 'acc) -> 'acc
  val fold_righti : ('k, 'v, _) t -> init:'acc -> f:(key:'k -> data:'v -> 'acc -> 'acc) -> 'acc
  val fold_map
    : ('k, 'v1, 'cmp) t -> init:'acc -> f:('acc -> 'v1 -> 'acc * 'v2) -> 'acc * ('k, 'v2, 'cmp) t
  val fold_mapi
    :  ('k, 'v1, 'cmp) t
    -> init:'acc
    -> f:('acc -> key:'k -> data:'v1 -> 'acc * 'v2)
    -> 'acc * ('k, 'v2, 'cmp) t

  val rekeying_map
    :  ('k1, 'v1, 'cmp1) t
    -> f:(key:'k1 -> data:'v1 -> 'k2 * 'v2)
    -> compare:('k2, 'cmp2) compare
    -> ('k2, 'v2, 'cmp2) t

  val find : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> 'v option
  val find_exn : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> 'v
  val mem : ('k, _, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> bool
  val find_and_call
    :  ('k, 'v, 'cmp) t
    -> 'k
    -> if_found:('v -> 'a)
    -> if_not_found:(unit -> 'a)
    -> compare:('k, 'cmp) compare
    -> 'a

  val add
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> compare:('k, 'cmp) compare
    -> [ `Ok of ('k, 'v, 'cmp) t | `Duplicate_key ]
  val add_exn
    : ('k, 'v, 'cmp) t -> key:'k -> data:'v -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val set
    : ('k, 'v, 'cmp) t -> key:'k -> data:'v -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val generic_add
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> on_already_present:(key:'k -> old_data:'v -> new_data:'v -> 'v)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) t

  val add_non_empty
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> compare:('k, 'cmp) compare
    -> [ `Ok of ('k, 'v, 'cmp) Non_empty.t | `Duplicate_key ]
  val add_non_empty_exn
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) Non_empty.t
  val set_non_empty
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) Non_empty.t
  val generic_add_non_empty
    :  ('k, 'v, 'cmp) t
    -> key:'k
    -> data:'v
    -> on_already_present:(key:'k -> old_data:'v -> new_data:'v -> 'v)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) Non_empty.t

  val remove : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t
  val find_and_remove
    : ('k, 'v, 'cmp) t -> 'k -> compare:('k, 'cmp) compare -> 'v option * ('k, 'v, 'cmp) t

  val union
    :  ('k, 'v, 'cmp) t
    -> ('k, 'v, 'cmp) t
    -> merge:(key:'k -> 'v -> 'v -> 'v)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v, 'cmp) t

  val inter
    :  ('k, 'v1, 'cmp) t
    -> ('k, 'v2, 'cmp) t
    -> merge:(key:'k -> 'v1 -> 'v2 -> 'v3)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v3, 'cmp) t

  val xor
    : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) t -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val remove_set
    : ('k, 'v, 'cmp) t -> ('k, 'cmp) set -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val restrict_to_set
    : ('k, 'v, 'cmp) t -> ('k, 'cmp) set -> compare:('k, 'cmp) compare -> ('k, 'v, 'cmp) t

  val filter_mapi : ('k, 'v1, 'cmp) t -> f:(key:'k -> data:'v1 -> 'v2 option) -> ('k, 'v2, 'cmp) t

  val generic_merge
    :  ('k, 'v1, 'cmp) t
    -> ('k, 'v2, 'cmp) t
    -> merge:(key:'k -> [ `Left of 'v1 | `Right of 'v2 | `Both of 'v1 * 'v2 ] -> 'v3 option)
    -> compare:('k, 'cmp) compare
    -> ('k, 'v3, 'cmp) t

  val find_min : ('k, 'v, _) t -> ('k * 'v) option
  val find_min_exn : ('k, 'v, _) t -> 'k * 'v
  val remove_min : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) t
  val find_and_remove_min : ('k, 'v, 'cmp) t -> ('k * 'v) option * ('k, 'v, 'cmp) t

  val find_max : ('k, 'v, _) t -> ('k * 'v) option
  val find_max_exn : ('k, 'v, _) t -> 'k * 'v
  val remove_max : ('k, 'v, 'cmp) t -> ('k, 'v, 'cmp) t
  val find_and_remove_max : ('k, 'v, 'cmp) t -> ('k * 'v) option * ('k, 'v, 'cmp) t
end

module type Specialized_non_empty_set = sig
  type 'a balanced_tree
  type ('a, 'cmp) generic_set
  type maybe_empty
  type elt
  type compare_witness

  val compare : (elt, compare_witness) compare

  type t = (elt, compare_witness) generic_set [@@deriving sexp_of]

  val height : t -> int
  val length : t -> int

  val singleton : elt -> t

  val to_list : t -> elt list

  val iter : t -> f:(elt -> unit) -> unit
  val fold : t -> init:'acc -> f:('acc -> elt -> 'acc) -> 'acc
  val fold_right : t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> 'acc

  val of_array : elt array -> t
  val of_sorted_array_unchecked : elt array -> t
  val of_sorted_array_exn : elt array -> t

  val of_list : elt list -> t
  val of_sorted_list_unchecked : elt list -> t
  val of_sorted_list_exn : elt list -> t

  val of_sorted_balanced_tree_unchecked : elt balanced_tree -> t
  val of_sorted_balanced_tree_exn : elt balanced_tree -> t
  val to_balanced_tree : t -> elt balanced_tree

  val resorting_map : ('a, _) generic_set -> f:('a -> elt) -> t
  val resorting_map' : t -> f:(elt -> 'a) -> compare:('a, 'cmp) compare -> ('a, 'cmp) generic_set

  val mem : t -> elt -> bool

  val add : t -> elt -> t
  val strict_add : t -> elt -> [ `Ok of t | `Duplicate_elt ]
  val strict_add_exn : t -> elt -> t
  val generic_add : t -> elt -> on_already_present:(elt -> unit) -> t

  val union : t -> t -> t

  val remove : t -> elt -> maybe_empty
  val strict_remove : t -> elt -> [ `Ok of maybe_empty | `Not_found ]
  val strict_remove_exn : t -> elt -> maybe_empty

  val inter : t -> t -> maybe_empty
  val xor : t -> t -> maybe_empty
  val diff : t -> t -> maybe_empty

  val find_min : t -> elt
  val remove_min : t -> maybe_empty
  val find_and_remove_min : t -> elt * maybe_empty

  val find_max : t -> elt
  val remove_max : t -> maybe_empty
  val find_and_remove_max : t -> elt * maybe_empty
end

module type Specialized_set = sig
  type 'a balanced_tree
  type 'a non_empty_balanced_tree
  type ('a, 'cmp) generic_set
  type ('a, 'cmp) non_empty_generic_set
  type elt
  type compare_witness

  val compare : (elt, compare_witness) compare

  type t = (elt, compare_witness) generic_set [@@deriving sexp_of]

  module Non_empty
    : Specialized_non_empty_set
      with type 'a balanced_tree := 'a non_empty_balanced_tree
      with type ('a, 'cmp) generic_set := ('a, 'cmp) non_empty_generic_set
      with type maybe_empty := t
      with type elt = elt
      with type compare_witness = compare_witness

  val height : t -> int
  val length : t -> int

  val singleton : elt -> t

  val to_list : t -> elt list

  val iter : t -> f:(elt -> unit) -> unit
  val fold : t -> init:'acc -> f:('acc -> elt -> 'acc) -> 'acc
  val fold_right : t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> 'acc

  val of_array : elt array -> t
  val of_sorted_array_unchecked : elt array -> t
  val of_sorted_array_exn : elt array -> t

  val of_list : elt list -> t
  val of_sorted_list_unchecked : elt list -> t
  val of_sorted_list_exn : elt list -> t

  val of_sorted_balanced_tree_unchecked : elt balanced_tree -> t
  val of_sorted_balanced_tree_exn : elt balanced_tree -> t
  val to_balanced_tree : t -> elt balanced_tree

  val resorting_map : ('a, _) generic_set -> f:('a -> elt) -> t
  val resorting_map' : t -> f:(elt -> 'a) -> compare:('a, 'cmp) compare -> ('a, 'cmp) generic_set

  val mem : t -> elt -> bool

  val add : t -> elt -> t
  val strict_add : t -> elt -> [ `Ok of t | `Duplicate_elt ]
  val strict_add_exn : t -> elt -> t
  val generic_add
    :  t
    -> elt
    -> on_already_present:(elt -> unit)
    -> t

  val union : t -> t -> t

  val empty : t

  val is_empty : t -> bool

  val of_non_empty : Non_empty.t -> t
  val of_non_empty_option : Non_empty.t option -> t
  val get_non_empty : t -> Non_empty.t option
  val get_non_empty_exn : t -> Non_empty.t

  val add_non_empty : t -> elt -> Non_empty.t
  val strict_add_non_empty : t -> elt -> [ `Ok of Non_empty.t | `Duplicate_elt ]
  val strict_add_non_empty_exn : t -> elt -> Non_empty.t
  val generic_add_non_empty : t -> elt -> on_already_present:(elt -> unit) -> Non_empty.t

  val remove : t -> elt -> t
  val strict_remove : t -> elt -> [ `Ok of t | `Not_found ]
  val strict_remove_exn : t -> elt -> t

  val inter : t -> t -> t
  val xor : t -> t -> t
  val diff : t -> t -> t

  val find_min : t -> elt option
  val find_min_exn : t -> elt
  val remove_min : t -> t
  val find_and_remove_min : t -> elt option * t

  val find_max : t -> elt option
  val find_max_exn : t -> elt
  val remove_max : t -> t
  val find_and_remove_max : t -> elt option * t
end

module type Specialized_non_empty_map = sig
  type ('a, 'b) balanced_tree
  type ('k, 'v, 'cmp) generic_map
  type key
  type compare_witness
  type set
  type 'a maybe_empty

  val compare : (key, compare_witness) compare

  type 'a t = (key, 'a, compare_witness) generic_map [@@deriving sexp_of]

  val height : _ t -> int
  val length : _ t -> int

  val singleton : key:key -> data:'a -> 'a t

  val of_array : (key * 'a) array -> 'a t
  val of_sorted_array_unchecked : (key * 'a) array -> 'a t
  val of_sorted_array_exn : (key * 'a) array -> 'a t

  val of_list : (key * 'a) list -> 'a t
  val of_sorted_list_unchecked : (key * 'a) list -> 'a t
  val of_sorted_list_exn : (key * 'a) list -> 'a t

  val of_sorted_balanced_tree_unchecked : (key, 'a) balanced_tree -> 'a t
  val of_sorted_balanced_tree_exn
    : (key, 'a) balanced_tree -> 'a t
  val to_balanced_tree : 'a t -> (key, 'a) balanced_tree

  val to_list : 'a t -> (key * 'a) list
  val keys : _ t -> key list
  val key_set : _ t -> set
  val data : 'a t -> 'a list

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val iter : 'a t -> f:('a -> unit) -> unit
  val iteri : 'a t -> f:(key:key -> data:'a -> unit) -> unit
  val fold : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val foldi : 'a t -> init:'acc -> f:('acc -> key:key -> data:'a -> 'acc) -> 'acc
  val fold_right : 'a t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold_righti : 'a t -> init:'acc -> f:(key:key -> data:'a -> 'acc -> 'acc) -> 'acc
  val fold_map
    : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t
  val fold_mapi
    :  'a t
    -> init:'acc
    -> f:('acc -> key:key -> data:'a -> 'acc * 'b)
    -> 'acc * 'b t

  val rekeying_map
    :  ('other_key, 'a, _) generic_map
    -> f:(key:'other_key -> data:'a -> key * 'b)
    -> 'b t

  val rekeying_map'
    :  'a t
    -> f:(key:key -> data:'a -> 'other_key * 'b)
    -> compare:('other_key, 'cmp) compare
    -> ('other_key, 'b, 'cmp) generic_map

  val find : 'a t -> key -> 'a option
  val find_exn : 'a t -> key -> 'a
  val mem : _ t -> key -> bool
  val find_and_call
    :  'a t
    -> key
    -> if_found:('a -> 'a)
    -> if_not_found:(unit -> 'a)
    -> 'a

  val add
    :  'a t
    -> key:key
    -> data:'a
    -> [ `Ok of 'a t | `Duplicate_key ]
  val add_exn : 'a t -> key:key -> data:'a -> 'a t
  val set : 'a t -> key:key -> data:'a -> 'a t
  val set' : 'a t -> key:key -> data:'a -> 'a t * Height_increase.t
  val generic_add
    :  'a t
    -> key:key
    -> data:'a
    -> on_already_present:(key:key -> old_data:'a -> new_data:'a -> 'a)
    -> 'a t

  val remove : 'a t -> key -> 'a maybe_empty
  val find_and_remove : 'a t -> key -> ('a * 'a maybe_empty) option

  (* CR wduff: These are kinda raw interfaces to be exposing here. In whatever form we keep them, we
     need them in the maybe_empty case as well. *)
  val join_into_left
    : 'a t -> key -> 'a -> 'a t -> height_difference:int -> 'a t * Height_increase.t
  val join_into_right
    : 'a t -> key -> 'a -> 'a t -> height_difference:int -> 'a t * Height_increase.t
  val join : 'a t -> int -> key -> 'a -> 'a t -> int -> 'a t * int
  val join0 : 'a t -> int -> 'a t -> int -> 'a t * int

  (* CR wduff: Add this to all the other relevant interfaces. *)
  val split : 'a t -> key -> 'a maybe_empty * int * 'a option * 'a maybe_empty * int

  val union : 'a t -> 'a t -> merge:(key:key -> 'a -> 'a -> 'a) -> 'a t
  val inter : 'a t -> 'b t -> merge:(key:key -> 'a -> 'b -> 'c) -> 'c maybe_empty
  val xor : 'a t -> 'a t -> 'a maybe_empty
  val remove_set : 'a t -> set -> 'a maybe_empty
  val restrict_to_set : 'a t -> set -> 'a maybe_empty

  val filter_mapi : 'a t -> f:(key:key -> data:'a -> 'b option) -> 'b maybe_empty

  val generic_merge
    :  'a t
    -> 'b t
    -> merge:(key:key -> [ `Left of 'a | `Right of 'b | `Both of 'a * 'b ] -> 'c option)
    -> 'c maybe_empty

  val find_min : 'a t -> key * 'a
  val remove_min : 'a t -> 'a maybe_empty
  val find_and_remove_min : 'a t -> (key * 'a) * 'a maybe_empty

  val find_max : 'a t -> key * 'a
  val remove_max : 'a t -> 'a maybe_empty
  val find_and_remove_max : 'a t -> (key * 'a) * 'a maybe_empty
end

module type Specialized_map = sig
  type ('a, 'b) balanced_tree
  type ('a, 'b) non_empty_balanced_tree
  type ('k, 'v, 'cmp) generic_map
  type ('k, 'v, 'cmp) non_empty_generic_map
  type key
  type compare_witness
  type set
  type non_empty_set

  val compare : (key, compare_witness) compare

  type 'a t = (key, 'a, compare_witness) generic_map [@@deriving sexp_of]

  module Non_empty
    : Specialized_non_empty_map
      with type set := non_empty_set
      with type ('a, 'b) balanced_tree := ('a, 'b) non_empty_balanced_tree
      with type ('k, 'v, 'cmp) generic_map := ('k, 'v, 'cmp) non_empty_generic_map
      with type 'a maybe_empty := 'a t
      with type key = key
      with type compare_witness = compare_witness

  val height : _ t -> int
  val length : _ t -> int

  val empty : _ t
  val is_empty : _ t -> bool

  val of_non_empty : 'a Non_empty.t -> 'a t
  val of_non_empty_option : 'a Non_empty.t option -> 'a t
  val get_non_empty : 'a t -> 'a Non_empty.t option
  val get_non_empty_exn : 'a t -> 'a Non_empty.t

  val singleton : key:key -> data:'a -> 'a t

  val of_array : (key * 'a) array -> 'a t
  val of_sorted_array_unchecked : (key * 'a) array -> 'a t
  val of_sorted_array_exn : (key * 'a) array -> 'a t

  val of_list : (key * 'a) list -> 'a t
  val of_sorted_list_unchecked : (key * 'a) list -> 'a t
  val of_sorted_list_exn : (key * 'a) list -> 'a t

  val of_sorted_balanced_tree_unchecked : (key, 'a) balanced_tree -> 'a t
  val of_sorted_balanced_tree_exn : (key, 'a) balanced_tree -> 'a t
  val to_balanced_tree : 'a t -> (key, 'a) balanced_tree

  val to_list : 'a t -> (key * 'a) list
  val keys : _ t -> key list
  val key_set : _ t -> set
  val data : 'a t -> 'a list

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val iter : 'a t -> f:('a -> unit) -> unit
  val iteri : 'a t -> f:(key:key -> data:'a -> unit) -> unit
  val fold : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val foldi : 'a t -> init:'acc -> f:('acc -> key:key -> data:'a -> 'acc) -> 'acc
  val fold_right : 'a t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
  val fold_righti : 'a t -> init:'acc -> f:(key:key -> data:'a -> 'acc -> 'acc) -> 'acc
  val fold_map
    : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t
  val fold_mapi
    :  'a t
    -> init:'acc
    -> f:('acc -> key:key -> data:'a -> 'acc * 'b)
    -> 'acc * 'b t

  val rekeying_map
    :  ('other_key, 'a, _) generic_map
    -> f:(key:'other_key -> data:'a -> key * 'b)
    -> 'b t

  val rekeying_map'
    :  'a t
    -> f:(key:key -> data:'a -> 'other_key * 'b)
    -> compare:('other_key, 'other_cmp) compare
    -> ('other_key, 'b, 'other_cmp) generic_map

  val find : 'a t -> key -> 'a option
  val find_exn : 'a t -> key -> 'a
  val mem : _ t -> key -> bool
  val find_and_call
    :  'a t
    -> key
    -> if_found:('a -> 'b)
    -> if_not_found:(unit -> 'b)
    -> 'b

  val add : 'a t -> key:key -> data:'a -> [ `Ok of 'a t | `Duplicate_key ]
  val add_exn : 'a t -> key:key -> data:'a -> 'a t
  val set : 'a t -> key:key -> data:'a -> 'a t
  val generic_add
    :  'a t
    -> key:key
    -> data:'a
    -> on_already_present:(key:key -> old_data:'a -> new_data:'a -> 'a)
    -> 'a t

  val add_non_empty : 'a t -> key:key -> data:'a -> [ `Ok of 'a Non_empty.t | `Duplicate_key ]
  val add_non_empty_exn : 'a t -> key:key -> data:'a -> 'a Non_empty.t
  val set_non_empty : 'a t -> key:key -> data:'a -> 'a Non_empty.t
  val generic_add_non_empty
    :  'a t
    -> key:key
    -> data:'a
    -> on_already_present:(key:key -> old_data:'a -> new_data:'a -> 'a)
    -> 'a Non_empty.t

  val remove : 'a t -> key -> 'a t
  val find_and_remove : 'a t -> key -> 'a option * 'a t

  val union : 'a t -> 'a t -> merge:(key:key -> 'a -> 'a -> 'a) -> 'a t
  val inter : 'a t -> 'b t -> merge:(key:key -> 'a -> 'b -> 'c) -> 'c t
  val xor : 'a t -> 'a t -> 'a t
  val remove_set : 'a t -> set -> 'a t
  val restrict_to_set : 'a t -> set -> 'a t

  val filter_mapi : 'a t -> f:(key:key -> data:'a -> 'b option) -> 'b t

  val generic_merge
    :  'a t
    -> 'b t
    -> merge:(key:key -> [ `Left of 'a | `Right of 'b | `Both of 'a * 'b ] -> 'c option)
    -> 'c t

  val find_min : 'a t -> (key * 'a) option
  val find_min_exn : 'a t -> key * 'a
  val remove_min : 'a t -> 'a t
  val find_and_remove_min : 'a t -> (key * 'a) option * 'a t

  val find_max : 'a t -> (key * 'a) option
  val find_max_exn : 'a t -> key * 'a
  val remove_max : 'a t -> 'a t
  val find_and_remove_max : 'a t -> (key * 'a) option * 'a t
end

module type Comparator = sig
  type t [@@deriving sexp_of]
  type compare_witness

  val compare : (t, compare_witness) compare
end

module type Brother_tree = sig
  module Tree : Tree

  module Tree2
    : Tree2
      with type 'a tree1 := 'a Tree.t
      with type 'a non_empty_tree1 := 'a Tree.Non_empty.t

  module Balanced_tree
    : Balanced_tree
      with type 'a raw_tree := 'a Tree.t
      with type 'a non_empty_raw_tree := 'a Tree.Non_empty.t

  module Balanced_tree2
    : Balanced_tree2
      with type 'a tree1 := 'a Balanced_tree.t
      with type 'a non_empty_tree1 := 'a Balanced_tree.Non_empty.t
      with type ('a, 'b) raw_tree := ('a, 'b) Tree2.t
      with type ('a, 'b) non_empty_raw_tree := ('a, 'b) Tree2.Non_empty.t

  module Set : sig
    include Set
      with type 'a balanced_tree := 'a Balanced_tree.t
      with type 'a non_empty_balanced_tree := 'a Balanced_tree.Non_empty.t

    module type Specialized =
      Specialized_set
      with type 'a balanced_tree := 'a Balanced_tree.t
      with type 'a non_empty_balanced_tree := 'a Balanced_tree.Non_empty.t
      with type ('a, 'cmp) generic_set := ('a, 'cmp) t
      with type ('a, 'cmp) non_empty_generic_set := ('a, 'cmp) Non_empty.t

    module Make (Elt : Comparable) : Specialized
      with type elt = Elt.t
      with type compare_witness = Compare.Make (Elt).compare_witness

    module Make_using_comparator (Elt : Comparator)
      : Specialized
        with type elt = Elt.t
        with type compare_witness = Elt.compare_witness
  end

  module Map : sig
    include Map
      with type ('a, 'cmp) set := ('a, 'cmp) Set.t
      with type ('a, 'cmp) non_empty_set := ('a, 'cmp) Set.Non_empty.t
      with type ('a, 'b) balanced_tree := ('a, 'b) Balanced_tree2.t
      with type ('a, 'b) non_empty_balanced_tree := ('a, 'b) Balanced_tree2.Non_empty.t

    module type Specialized =
      Specialized_map
        with type ('a, 'b) balanced_tree := ('a, 'b) Balanced_tree2.t
        with type ('a, 'b) non_empty_balanced_tree := ('a, 'b) Balanced_tree2.Non_empty.t
        with type ('k, 'v, 'cmp) generic_map := ('k, 'v, 'cmp) t
        with type ('k, 'v, 'cmp) non_empty_generic_map := ('k, 'v, 'cmp) Non_empty.t

    module Make (Key : Comparable)
      : Specialized
        with type key = Key.t
        with type compare_witness = Compare.Make (Key).compare_witness
        with type set = (Key.t, Compare.Make (Key).compare_witness) Set.t
        with type non_empty_set = (Key.t, Compare.Make (Key).compare_witness) Set.Non_empty.t

    module Make_using_comparator (Key : Comparator)
      : Specialized
        with type key = Key.t
        with type compare_witness = Key.compare_witness
        with type set = (Key.t, Key.compare_witness) Set.t
        with type non_empty_set = (Key.t, Key.compare_witness) Set.Non_empty.t
  end
end
