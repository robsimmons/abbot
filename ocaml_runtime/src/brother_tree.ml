open! Base
open Brother_tree_intf

module Tree : Tree = struct
  module Non_empty : Non_empty_tree = struct
    type 'a t =
      | Leaf1 of 'a
      | Leaf2 of 'a * 'a
      | Two of 'a t * 'a * 'a t
      | OneTwo of 'a t * 'a * 'a t
      | TwoOne of 'a t * 'a * 'a t

    let rec length t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (left, _, right) | OneTwo (left, _, right) | TwoOne (left, _, right) ->
        length left + 1 + length right
    ;;

    let singleton a = Leaf1 a

    let rec of_array_slice array ~start ~end_ =
      let length = end_ - start in
      match length with
      | 1 -> Leaf1 array.(start)
      | 2 -> Leaf2 (array.(start), array.(start + 1))
      | _ ->
        let mid = (start + end_) / 2 in
        let a = array.(mid) in
        let left = of_array_slice array ~start ~end_:mid in
        let right = of_array_slice array ~start:(mid + 1) ~end_ in
        if Int.is_pow2 length
        then TwoOne (left, a, right)
        else Two (left, a, right)
    ;;

    let of_array array =
      of_array_slice array ~start:0 ~end_:(Array.length array)
    ;;

    (* CR wduff: Is there a faster way to do this? *)
    let of_list list = of_array (Array.of_list list)

    let rec map t ~f =
      match t with
      | Leaf1 a ->
        let a = f a in
        Leaf1 a
      | Leaf2 (a1, a2) ->
        let a1 = f a1 in
        let a2 = f a2 in
        Leaf2 (a1, a2)
      | Two (left, a, right) ->
        let left = map left ~f in
        let a = f a in
        let right = map right ~f in
        Two (left, a, right)
      | OneTwo (left, a, right) ->
        let left = map left ~f in
        let a = f a in
        let right = map right ~f in
        OneTwo (left, a, right)
      | TwoOne (left, a, right) ->
        let left = map left ~f in
        let a = f a in
        let right = map right ~f in
        TwoOne (left, a, right)
    ;;

    let rec iter t ~f =
      match t with
      | Leaf1 a -> f a
      | Leaf2 (a1, a2) ->
        f a1;
        f a2
      | Two (left, a, right)
      | OneTwo (left, a, right)
      | TwoOne (left, a, right)
        ->
        iter left ~f;
        f a;
        iter right ~f
    ;;

    let rec fold t ~init ~f =
      match t with
      | Leaf1 a -> f init a
      | Leaf2 (a1, a2) ->
        let acc = f init a1  in
        f acc a2
      | Two (left, a, right)
      | OneTwo (left, a, right)
      | TwoOne (left, a, right)
        ->
        let acc = fold left ~init ~f in
        let acc = f acc a  in
        fold right ~init:acc ~f
    ;;

    let rec fold_right t ~init ~f =
      match t with
      | Leaf1 a -> f a init
      | Leaf2 (a1, a2) ->
        let acc = f a2 init in
        f a1 acc
      | Two (left, a, right)
      | OneTwo (left, a, right)
      | TwoOne (left, a, right)
        ->
        let acc = fold_right right ~init ~f in
        let acc = f a acc in
        fold_right left ~init:acc ~f
    ;;

    let rec fold_map t ~init ~f =
      match t with
      | Leaf1 a ->
        let (acc, a) = f init a in
        (acc, Leaf1 a)
      | Leaf2 (a1, a2) ->
        let (acc, a1) = f init a1 in
        let (acc, a2) = f acc a2 in
        (acc, Leaf2 (a1, a2))
      | Two (left, a, right) ->
        let (acc, left) = fold_map left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map right ~init:acc ~f in
        (acc, Two (left, a, right))
      | OneTwo (left, a, right) ->
        let (acc, left) = fold_map left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map right ~init:acc ~f in
        (acc, OneTwo (left, a, right))
      | TwoOne (left, a, right) ->
        let (acc, left) = fold_map left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map right ~init:acc ~f in
        (acc, TwoOne (left, a, right))
    ;;

    let to_list t =
      fold_right t ~init:[] ~f:(fun a acc -> a :: acc)
    ;;

    let sexp_of_t sexp_of_a t =
      [%sexp_of: a list] (to_list t)
    ;;

    let rec find_leftmost t =
      match t with
      | Leaf1 a | Leaf2 (a, _) -> a
      | Two (left, _, _) | OneTwo (left, _, _) | TwoOne (left, _, _) ->
        find_leftmost left
    ;;

    let rec find_rightmost t =
      match t with
      | Leaf1 a | Leaf2 (_, a) -> a
      | Two (_, _, right) | OneTwo (_, _, right) | TwoOne (_, _, right) ->
        find_rightmost right
    ;;
  end

  type 'a t = 'a Non_empty.t option


  let length t =
    match t with
    | None -> 0
    | Some non_empty -> Non_empty.length non_empty
  ;;

  let empty = None
  let is_empty = Option.is_none

  let singleton a = Some (Non_empty.singleton a)

  let of_non_empty non_empty = Some non_empty
  let of_non_empty_option = Fn.id
  let get_non_empty = Fn.id
  (* CR wduff: Better error message? *)
  let get_non_empty_exn t = Option.value_exn t


  let of_array array =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_array array)
  ;;

  let of_list list =
    if List.is_empty list
    then None
    else Some (Non_empty.of_list list)
  ;;

  let map t ~f =
    Option.map t ~f:(Non_empty.map ~f)
  ;;

  let iter t ~f =
    Option.iter t ~f:(Non_empty.iter ~f)
  ;;

  let fold t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold non_empty ~init ~f)
  ;;

  let fold_right t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold_right non_empty ~init ~f)
  ;;

  let fold_map t ~init ~f =
    match t with
    | None -> (init, None)
    | Some non_empty ->
      let (acc, non_empty) = Non_empty.fold_map non_empty ~init ~f in
      (acc, Some non_empty)
  ;;

  let to_list t =
    match t with
    | None -> []
    | Some non_empty -> Non_empty.to_list non_empty
  ;;

  let sexp_of_t sexp_of_a t =
    [%sexp_of: a list] (to_list t)
  ;;

  let find_leftmost t =
    Option.map t ~f:Non_empty.find_leftmost
  ;;

  let find_leftmost_exn t =
    get_non_empty_exn t
    |> Non_empty.find_leftmost
  ;;

  let find_rightmost t =
    Option.map t ~f:Non_empty.find_rightmost
  ;;

  let find_rightmost_exn t =
    get_non_empty_exn t
    |> Non_empty.find_rightmost
  ;;
end

module Tree2 : Tree2
  with type 'a tree1 := 'a Tree.t
  with type 'a non_empty_tree1 := 'a Tree.Non_empty.t
=
struct
  module Non_empty : Non_empty_tree2 with type 'a tree1 := 'a Tree.Non_empty.t = struct
    type ('a, 'b) t =
      | Leaf1 of 'a * 'b
      | Leaf2 of 'a * 'b * 'a * 'b
      | Two of ('a, 'b) t * 'a * 'b * ('a, 'b) t
      | OneTwo of ('a, 'b) t * 'a * 'b * ('a, 'b) t
      | TwoOne of ('a, 'b) t * 'a * 'b * ('a, 'b) t
    [@@deriving sexp_of]

    let rec length t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (left, _, _, right) | OneTwo (left, _, _, right) | TwoOne (left, _, _, right) ->
        length left + 1 + length right
    ;;

    let singleton a b = Leaf1 (a, b)

    let rec of_array_slice array ~start ~end_ =
      let length = end_ - start in
      match length with
      | 1 ->
        let (a, b) = array.(start) in
        Leaf1 (a, b)
      | 2 ->
        let (a1, b1) = array.(start) in
        let (a2, b2) = array.(start + 1) in
        Leaf2 (a1, b1, a2, b2)
      | _ ->
        let mid = (start + end_) / 2 in
        let (a, b) = array.(mid) in
        let left = of_array_slice array ~start ~end_:mid in
        let right = of_array_slice array ~start:(mid + 1) ~end_ in
        if Int.is_pow2 length
        then TwoOne (left, a, b, right)
        else Two (left, a, b, right)
    ;;

    let of_array array =
      of_array_slice array ~start:0 ~end_:(Array.length array)
    ;;

    (* CR wduff: Is there a faster way to do this? *)
    let of_list list = of_array (Array.of_list list)

    let rec find_leftmost t =
      match t with
      | Leaf1 (a, b) | Leaf2 (a, b, _, _) -> (a, b)
      | Two (left, _, _, _) | OneTwo (left, _, _, _) | TwoOne (left, _, _, _) ->
        find_leftmost left
    ;;

    let rec find_rightmost t =
      match t with
      | Leaf1 (a, b) | Leaf2 (_, _, a, b) -> (a, b)
      | Two (_, _, _, right) | OneTwo (_, _, _, right) | TwoOne (_, _, _, right) ->
        find_rightmost right
    ;;

    let rec map_both t ~f =
      match t with
      | Leaf1 (a, b) ->
        let (a, b) = f a b in
        Leaf1 (a, b)
      | Leaf2 (a1, b1, a2, b2) ->
        let (a1, b1) = f a1 b1 in
        let (a2, b2) = f a2 b2 in
        Leaf2 (a1, b1, a2, b2)
      | Two (left, a, b, right) ->
        let left = map_both left ~f in
        let (a, b) = f a b in
        let right = map_both right ~f in
        Two (left, a, b, right)
      | OneTwo (left, a, b, right) ->
        let left = map_both left ~f in
        let (a, b) = f a b in
        let right = map_both right ~f in
        OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right) ->
        let left = map_both left ~f in
        let (a, b) = f a b in
        let right = map_both right ~f in
        TwoOne (left, a, b, right)
    ;;

    let rec map1 t ~f =
      match t with
      | Leaf1 (a, b) -> Leaf1 (f a, b)
      | Leaf2 (a1, b1, a2, b2) ->
        let a1 = f a1 in
        let a2 = f a2 in
        Leaf2 (a1, b1, a2, b2)
      | Two (left, a, b, right) ->
        let left = map1 left ~f in
        let a = f a in
        let right = map1 right ~f in
        Two (left, a, b, right)
      | OneTwo (left, a, b, right) ->
        let left = map1 left ~f in
        let a = f a in
        let right = map1 right ~f in
        OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right) ->
        let left = map1 left ~f in
        let a = f a in
        let right = map1 right ~f in
        TwoOne (left, a, b, right)
    ;;

    (* CR wduff: This is a sad name conflict. *)
    let rec map2 t ~f =
      match t with
      | Leaf1 (a, b) -> Leaf1 (a, f b)
      | Leaf2 (a1, b1, a2, b2) ->
        let b1 = f b1 in
        let b2 = f b2 in
        Leaf2 (a1, b1, a2, b2)
      | Two (left, a, b, right) ->
        let left = map2 left ~f in
        let b = f b in
        let right = map2 right ~f in
        Two (left, a, b, right)
      | OneTwo (left, a, b, right) ->
        let left = map2 left ~f in
        let b = f b in
        let right = map2 right ~f in
        OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right) ->
        let left = map2 left ~f in
        let b = f b in
        let right = map2 right ~f in
        TwoOne (left, a, b, right)
    ;;

    let rec iter_both t ~f =
      match t with
      | Leaf1 (a, b) -> f a b
      | Leaf2 (a1, b1, a2, b2) ->
        f a1 b1;
        f a2 b2
      | Two (left, a, b, right)
      | OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right)
        ->
        iter_both left ~f;
        f a b;
        iter_both right ~f
    ;;

    let iter1 t ~f = iter_both t ~f:(fun a _ -> f a)
    let iter2 t ~f = iter_both t ~f:(fun _ b -> f b)

    let rec fold_both t ~init ~f =
      match t with
      | Leaf1 (a, b) -> f init a b
      | Leaf2 (a1, b1, a2, b2) ->
        let acc = f init a1 b1  in
        f acc a2 b2
      | Two (left, a, b, right)
      | OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right)
        ->
        let acc = fold_both left ~init ~f in
        let acc = f acc a b  in
        fold_both right ~init:acc ~f
    ;;

    let fold1 t ~init ~f = fold_both t ~init ~f:(fun acc a _ -> f acc a)
    let fold2 t ~init ~f = fold_both t ~init ~f:(fun acc _ b -> f acc b)

    let rec fold_both_right t ~init ~f =
      match t with
      | Leaf1 (a, b) -> f a b init
      | Leaf2 (a1, b1, a2, b2) ->
        let acc = f a2 b2 init in
        f a1 b1 acc
      | Two (left, a, b, right)
      | OneTwo (left, a, b, right)
      | TwoOne (left, a, b, right)
        ->
        let acc = fold_both_right right ~init ~f in
        let acc = f a b acc in
        fold_both_right left ~init:acc ~f
    ;;

    let fold1_right t ~init ~f = fold_both_right t ~init ~f:(fun a _ acc -> f a acc)
    let fold2_right t ~init ~f = fold_both_right t ~init ~f:(fun _ b acc -> f b acc)

    let rec fold_map_both t ~init ~f =
      match t with
      | Leaf1 (a, b) ->
        let (acc, a, b) = f init a b in
        (acc, Leaf1 (a, b))
      | Leaf2 (a1, b1, a2, b2) ->
        let (acc, a1, b1) = f init a1 b1 in
        let (acc, a2, b2) = f acc a2 b2 in
        (acc, Leaf2 (a1, b1, a2, b2))
      | Two (left, a, b, right) ->
        let (acc, left) = fold_map_both left ~init ~f in
        let (acc, a, b) = f acc a b in
        let (acc, right) = fold_map_both right ~init:acc ~f in
        (acc, Two (left, a, b, right))
      | OneTwo (left, a, b, right) ->
        let (acc, left) = fold_map_both left ~init ~f in
        let (acc, a, b) = f acc a b in
        let (acc, right) = fold_map_both right ~init:acc ~f in
        (acc, OneTwo (left, a, b, right))
      | TwoOne (left, a, b, right) ->
        let (acc, left) = fold_map_both left ~init ~f in
        let (acc, a, b) = f acc a b in
        let (acc, right) = fold_map_both right ~init:acc ~f in
        (acc, TwoOne (left, a, b, right))
    ;;

    let rec fold_map1 t ~init ~f =
      match t with
      | Leaf1 (a, b) ->
        let (acc, a) = f init a in
        (acc, Leaf1 (a, b))
      | Leaf2 (a1, b1, a2, b2) ->
        let (acc, a1) = f init a1 in
        let (acc, a2) = f acc a2 in
        (acc, Leaf2 (a1, b1, a2, b2))
      | Two (left, a, b, right) ->
        let (acc, left) = fold_map1 left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map1 right ~init:acc ~f in
        (acc, Two (left, a, b, right))
      | OneTwo (left, a, b, right) ->
        let (acc, left) = fold_map1 left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map1 right ~init:acc ~f in
        (acc, OneTwo (left, a, b, right))
      | TwoOne (left, a, b, right) ->
        let (acc, left) = fold_map1 left ~init ~f in
        let (acc, a) = f acc a in
        let (acc, right) = fold_map1 right ~init:acc ~f in
        (acc, TwoOne (left, a, b, right))
    ;;

    let rec fold_map2 t ~init ~f =
      match t with
      | Leaf1 (a, b) ->
        let (acc, b) = f init b in
        (acc, Leaf1 (a, b))
      | Leaf2 (a1, b1, a2, b2) ->
        let (acc, b1) = f init b1 in
        let (acc, b2) = f acc b2 in
        (acc, Leaf2 (a1, b1, a2, b2))
      | Two (left, a, b, right) ->
        let (acc, left) = fold_map2 left ~init ~f in
        let (acc, b) = f acc b in
        let (acc, right) = fold_map2 right ~init:acc ~f in
        (acc, Two (left, a, b, right))
      | OneTwo (left, a, b, right) ->
        let (acc, left) = fold_map2 left ~init ~f in
        let (acc, b) = f acc b in
        let (acc, right) = fold_map2 right ~init:acc ~f in
        (acc, OneTwo (left, a, b, right))
      | TwoOne (left, a, b, right) ->
        let (acc, left) = fold_map2 left ~init ~f in
        let (acc, b) = f acc b in
        let (acc, right) = fold_map2 right ~init:acc ~f in
        (acc, TwoOne (left, a, b, right))
    ;;

    let to_pair_list t =
      fold_both_right t ~init:[] ~f:(fun a b acc -> (a, b) :: acc)
    ;;

    let to_list1 t =
      fold1_right t ~init:[] ~f:(fun a acc -> a :: acc)
    ;;

    let to_list2 t =
      fold2_right t ~init:[] ~f:(fun b acc -> b :: acc)
    ;;

    (* CR wduff:
       let sexp_of_t sexp_of_a sexp_of_b t =
       [%sexp_of: (a * b) list] (to_pair_list t)
       ;;
    *)

    (* CR wduff: Find a better name for these. *)
    let rec to_pair_tree (t : ('a, 'b) t) : ('a * 'b) Tree.Non_empty.t =
      match t with
      | Leaf1 (a, b) -> Leaf1 (a, b)
      | Leaf2 (a1, b1, a2, b2) -> Leaf2 ((a1, b1), (a2, b2))
      | Two (left, a, b, right) -> Two (to_pair_tree left, (a, b), to_pair_tree right)
      | OneTwo (left, a, b, right) -> OneTwo (to_pair_tree left, (a, b), to_pair_tree right)
      | TwoOne (left, a, b, right) -> TwoOne (to_pair_tree left, (a, b), to_pair_tree right)
    ;;

    let rec to_tree1 (t : ('a, 'b) t) : 'a Tree.Non_empty.t =
      match t with
      | Leaf1 (a, _) -> Leaf1 a
      | Leaf2 (a1, _, a2, _) -> Leaf2 (a1, a2)
      | Two (left, a, _, right) -> Two (to_tree1 left, a, to_tree1 right)
      | OneTwo (left, a, _, right) -> OneTwo (to_tree1 left, a, to_tree1 right)
      | TwoOne (left, a, _, right) -> TwoOne (to_tree1 left, a, to_tree1 right)
    ;;

    let rec to_tree2 (t : ('a, 'b) t) : 'b Tree.Non_empty.t =
      match t with
      | Leaf1 (_, b) -> Leaf1 b
      | Leaf2 (_, b1, _, b2) -> Leaf2 (b1, b2)
      | Two (left, _, b, right) -> Two (to_tree2 left, b, to_tree2 right)
      | OneTwo (left, _, b, right) -> OneTwo (to_tree2 left, b, to_tree2 right)
      | TwoOne (left, _, b, right) -> TwoOne (to_tree2 left, b, to_tree2 right)
    ;;
  end

  type ('a, 'b) t = ('a, 'b) Non_empty.t option [@@deriving sexp_of]

  let length t =
    match t with
    | None -> 0
    | Some non_empty -> Non_empty.length non_empty
  ;;

  let empty = None
  let is_empty = Option.is_none
  let of_non_empty non_empty = Some non_empty
  let of_non_empty_option = Fn.id
  let get_non_empty = Fn.id
  (* CR wduff: Better error message? *)
  let get_non_empty_exn t = Option.value_exn t

  let singleton a b = Some (Non_empty.singleton a b)

  let of_array array =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_array array)
  ;;

  let of_list list =
    if List.is_empty list
    then None
    else Some (Non_empty.of_list list)
  ;;

  let to_pair_list t =
    match t with
    | None -> []
    | Some non_empty -> Non_empty.to_pair_list non_empty
  ;;

  let to_list1 t =
    match t with
    | None -> []
    | Some non_empty -> Non_empty.to_list1 non_empty
  ;;

  let to_list2 t =
    match t with
    | None -> []
    | Some non_empty -> Non_empty.to_list2 non_empty
  ;;

  (* CR wduff:
     let sexp_of_t sexp_of_a sexp_of_b t =
     [%sexp_of: (a * b) list] (to_pair_list t)
     ;;
  *)

  let to_pair_tree t =
    match t with
    | None -> None
    | Some non_empty -> Some (Non_empty.to_pair_tree non_empty)
  ;;

  let to_tree1 t =
    match t with
    | None -> None
    | Some non_empty -> Some (Non_empty.to_tree1 non_empty)
  ;;

  let to_tree2 t =
    match t with
    | None -> None
    | Some non_empty -> Some (Non_empty.to_tree2 non_empty)
  ;;

  let map_both t ~f =
    Option.map t ~f:(Non_empty.map_both ~f)
  ;;

  let map1 t ~f =
    Option.map t ~f:(Non_empty.map1 ~f)
  ;;

  let map2 t ~f =
    Option.map t ~f:(Non_empty.map2 ~f)
  ;;

  let iter_both t ~f =
    Option.iter t ~f:(Non_empty.iter_both ~f)
  ;;

  let iter1 t ~f =
    Option.iter t ~f:(Non_empty.iter1 ~f)
  ;;

  let iter2 t ~f =
    Option.iter t ~f:(Non_empty.iter2 ~f)
  ;;

  let fold_both t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold_both non_empty ~init ~f)
  ;;

  let fold1 t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold1 non_empty ~init ~f)
  ;;

  let fold2 t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold2 non_empty ~init ~f)
  ;;

  let fold_both_right t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold_both_right non_empty ~init ~f)
  ;;

  let fold1_right t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold1_right non_empty ~init ~f)
  ;;

  let fold2_right t ~init ~f =
    Option.fold t ~init ~f:(fun init non_empty -> Non_empty.fold2_right non_empty ~init ~f)
  ;;

  let fold_map_both t ~init ~f =
    match t with
    | None -> (init, None)
    | Some non_empty ->
      let (acc, non_empty) = Non_empty.fold_map_both non_empty ~init ~f in
      (acc, Some non_empty)
  ;;

  let fold_map1 t ~init ~f =
    match t with
    | None -> (init, None)
    | Some non_empty ->
      let (acc, non_empty) = Non_empty.fold_map1 non_empty ~init ~f in
      (acc, Some non_empty)
  ;;

  let fold_map2 t ~init ~f =
    match t with
    | None -> (init, None)
    | Some non_empty ->
      let (acc, non_empty) = Non_empty.fold_map2 non_empty ~init ~f in
      (acc, Some non_empty)
  ;;

  let find_leftmost t =
    Option.map t ~f:Non_empty.find_leftmost
  ;;

  let find_rightmost t =
    Option.map t ~f:Non_empty.find_rightmost
  ;;

  let find_leftmost_exn t =
    get_non_empty_exn t
    |> Non_empty.find_leftmost
  ;;

  let find_rightmost_exn t =
    get_non_empty_exn t
    |> Non_empty.find_rightmost
  ;;
end

open Height_increase
open Height_decrease

(* CR wduff: Put module ascriptions in various places to demonstrate that we can implement
   everything purely using the interfaces. *)
module Balanced_tree(* : Balanced_tree
  with type 'a raw_tree := 'a Tree.t
  with type 'a non_empty_raw_tree := 'a Tree.Non_empty.t
  with type 'a t = 'a Tree.t
  with type 'a Non_empty.t = 'a Tree.Non_empty.t *)=
struct
  include (Tree : Tree with module Non_empty := Tree.Non_empty)

  module Non_empty(* : Non_empty_balanced_tree
    with type 'a raw_tree := 'a Tree.Non_empty.t
    with type 'a maybe_empty := 'a t
    with type 'a t = 'a Tree.Non_empty.t *)=
  struct
    include Tree.Non_empty

    (* CR wduff: Insert invariant checks around toplevel functions controlled by a debug flag. *)
    (* CR wduff: Better error messages. *)
    let rec height_invariant t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (left, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        assert (left_height = right_height);
        left_height + 1
      | OneTwo (left, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        assert (left_height + 1 = right_height);
        right_height + 1
      | TwoOne (left, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        assert (left_height = right_height + 1);
        left_height + 1
    ;;

    let of_balanced_raw_tree_unchecked raw_tree = raw_tree

    let of_balanced_raw_tree_exn raw_tree =
      ignore (height_invariant raw_tree : int);
      of_balanced_raw_tree_unchecked raw_tree
    ;;

    let to_raw_tree t = t

    let rec height t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (_, _, right) -> height right + 1
      | OneTwo (left, _, _) -> height left + 2
      | TwoOne (_, _, right) -> height right + 2
    ;;

    let rebalance_left_is_2_shorter' left elt right =
      match right with
      | Leaf1 _ | Leaf2 _ | Two _ ->
        (* Since left is a [Non_empty.t], [height left >= 1], so since
           [height right = height left + 2], [height right >= 3].
           Further, a height increase can never result in a [Two] node. *)
        assert false
      | OneTwo (right_left, elt', right_right) ->
        Two (Two (left, elt, right_left), elt', right_right)
      | TwoOne (right_left, elt', right_right) ->
        match right_left with
        | Leaf1 _ ->
          (* Since [height right >= 3], [height right_left >= 2]. *)
          assert false
        | Leaf2 (elt1, elt2) ->
          (match right_right with
           | Leaf1 elt'' ->
             Two (Two (left, elt, Leaf1 elt1), elt2, Leaf2 (elt', elt''))
           | _ ->
             (* Since [height right_left = 2], [height right_right = 1]. *)
             assert false)
        | Two (right_left_left, elt'', right_left_right) ->
          Two
            (Two (left, elt, right_left_left),
             elt'',
             Two (right_left_right, elt', right_right))
        | OneTwo (right_left_left, elt'', right_left_right) ->
          Two
            (TwoOne (left, elt, right_left_left),
             elt'',
             Two (right_left_right, elt', right_right))
        | TwoOne (right_left_left, elt'', right_left_right) ->
          Two
            (Two (left, elt, right_left_left),
             elt'',
             OneTwo (right_left_right, elt', right_right))
    ;;

    let rebalance_left_is_2_shorter left elt right =
      match right with
      | Two (right_left, elt', right_right) ->
        (TwoOne (OneTwo (left, elt, right_left), elt', right_right), Height_unchanged)
      | _ ->
        (rebalance_left_is_2_shorter' left elt right, Height_decreased)
    ;;

    let rebalance_right_is_2_shorter' left elt right =
      match left with
      | Leaf1 _ | Leaf2 _ | Two _ ->
        (* Since right is a [Non_empty.t], [height right >= 1], so since
           [height left = height right + 2], [height left >= 3].
           Further, a height increase can never result in a [Two] node. *)
        assert false
      | TwoOne (left_left, elt', left_right) ->
        Two (left_left, elt', Two (left_right, elt, right))
      | OneTwo (left_left, elt', left_right) ->
        match left_right with
        | Leaf1 _ ->
          (* Since [height left >= 3], [height left_right >= 2]. *)
          assert false
        | Leaf2 (elt1, elt2) ->
          (match left_left with
           | Leaf1 elt'' ->
             Two (Leaf2 (elt'', elt'), elt1, Two (Leaf1 elt2, elt, right))
           | _ ->
             (* Since [height left_right = 2], [height left_left = 1]. *)
             assert false)
        | Two (left_right_left, elt'', left_right_right) ->
          Two
            (Two (left_left, elt', left_right_left),
             elt'',
             Two (left_right_right, elt, right))
        | OneTwo (left_right_right, elt'', left_right_left) ->
          Two
            (TwoOne (left_left, elt', left_right_left),
             elt'',
             Two (left_right_right, elt, right))
        | TwoOne (left_right_right, elt'', left_right_left) ->
          Two
            (Two (left_left, elt', left_right_left),
             elt'',
             OneTwo (left_right_right, elt, right))
    ;;

    let rebalance_right_is_2_shorter left elt right =
      match left with
      | Two (left_left, elt', left_right) ->
        (TwoOne (left_left, elt', OneTwo (left_right, elt, right)), Height_unchanged)
      | _ ->
        (rebalance_right_is_2_shorter' left elt right, Height_decreased)
    ;;

    let two_left_maybe_grew (left, height_increased) elt right : _ * Height_increase.t =
      match (height_increased : Height_increase.t) with
      | Height_unchanged -> (Two (left, elt, right), Height_unchanged)
      | Height_increased -> (TwoOne (left, elt, right), Height_increased)
    ;;

    let one_two_left_maybe_grew (left, height_increased) elt right : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged -> OneTwo (left, elt, right)
        | Height_increased -> Two (left, elt, right)
      in
      (t, Height_unchanged)
    ;;

    let two_one_left_maybe_grew (left, height_increased) elt right : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged -> TwoOne (left, elt, right)
        | Height_increased -> rebalance_right_is_2_shorter' left elt right
      in
      (t, Height_unchanged)
    ;;

    let two_right_maybe_grew left elt (right, height_increased) : _ * Height_increase.t =
      match (height_increased : Height_increase.t) with
      | Height_unchanged -> (Two (left, elt, right), Height_unchanged)
      | Height_increased -> (OneTwo (left, elt, right), Height_increased)
    ;;

    let one_two_right_maybe_grew left elt (right, height_increased) : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged -> OneTwo (left, elt, right)
        | Height_increased -> rebalance_left_is_2_shorter' left elt right
      in
      (t, Height_unchanged)
    ;;

    let two_one_right_maybe_grew left elt (right, height_increased) : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged -> TwoOne (left, elt, right)
        | Height_increased -> Two (left, elt, right)
      in
      (t, Height_unchanged)
    ;;

    let two_left_maybe_shrank left_opt elt right =
      let t =
        match left_opt with
        | None ->
          (match right with
           | Leaf1 elt' -> Leaf2 (elt, elt')
           | _ -> assert false)
        | Some (left, height_decreased) ->
          match height_decreased with
          | Height_unchanged -> Two (left, elt, right)
          | Height_decreased -> OneTwo (left, elt, right)
      in
      (t, Height_unchanged)
    ;;

    let one_two_left_maybe_shrank left_opt elt right =
      match left_opt with
      | None ->
        (match right with
         | Leaf2 (elt1, elt2) ->
           (Two (Leaf1 elt, elt1, Leaf1 elt2), Height_decreased)
         | Two (Leaf1 elt1, elt2, right_right) ->
           (TwoOne (Leaf2 (elt, elt1), elt2, right_right), Height_unchanged)
         | _ -> assert false)
      | Some (left, height_decreased) ->
        match height_decreased with
        | Height_unchanged -> (OneTwo (left, elt, right), Height_unchanged)
        | Height_decreased -> rebalance_left_is_2_shorter left elt right
    ;;

    let two_one_left_maybe_shrank left_opt elt right =
      match left_opt with
      | None -> assert false
      | Some (left, height_decreased) ->
        match height_decreased with
        | Height_unchanged -> (TwoOne (left, elt, right), Height_unchanged)
        | Height_decreased -> (Two (left, elt, right), Height_decreased)
    ;;

    let two_right_maybe_shrank left elt right_opt =
      let t =
        match right_opt with
        | None ->
          (match left with
           | Leaf1 elt' -> Leaf2 (elt, elt')
           | _ -> assert false)
        | Some (right, height_decreased) ->
          match height_decreased with
          | Height_unchanged -> Two (left, elt, right)
          | Height_decreased -> TwoOne (left, elt, right)
      in
      (t, Height_unchanged)
    ;;

    let one_two_right_maybe_shrank left elt right_opt =
      match right_opt with
      | None -> assert false
      | Some (right, height_decreased) ->
        match height_decreased with
        | Height_unchanged -> (OneTwo (left, elt, right), Height_unchanged)
        | Height_decreased -> (Two (left, elt, right), Height_decreased)
    ;;

    let two_one_right_maybe_shrank left elt right_opt =
      match right_opt with
      | None ->
        (match left with
         | Leaf2 (elt1, elt2) ->
           (Two (Leaf1 elt1, elt2, Leaf1 elt), Height_decreased)
         | Two (Leaf1 elt1, elt2, right_right) ->
           (TwoOne (Leaf2 (elt1, elt2), elt, right_right), Height_unchanged)
         | _ -> assert false)
      | Some (right, height_decreased) ->
        match height_decreased with
        | Height_unchanged -> (TwoOne (left, elt, right), Height_unchanged)
        | Height_decreased -> rebalance_right_is_2_shorter left elt right
    ;;

    let rec remove_leftmost' t =
      match t with
      | Leaf1 _ -> None
      | Leaf2 (_, elt2) -> Some (Leaf1 elt2, Height_decreased)
      | Two (left, elt, right) ->
        Some (two_left_maybe_shrank (remove_leftmost' left) elt right)
      | OneTwo (left, elt, right) ->
        Some (one_two_left_maybe_shrank (remove_leftmost' left) elt right)
      | TwoOne (left, elt, right) ->
        Some (two_one_left_maybe_shrank (remove_leftmost' left) elt right)
    ;;

    let remove_leftmost t =
      Option.map (remove_leftmost' t) ~f:fst
    ;;

    let rec remove_rightmost' t =
      match t with
      | Leaf1 _ -> None
      | Leaf2 (elt1, _) -> Some (Leaf1 elt1, Height_decreased)
      | Two (left, elt, right) ->
        Some (two_right_maybe_shrank left elt (remove_rightmost' right))
      | OneTwo (left, elt, right) ->
        Some (one_two_right_maybe_shrank left elt (remove_rightmost' right))
      | TwoOne (left, elt, right) ->
        Some (two_one_right_maybe_shrank left elt (remove_rightmost' right))
    ;;

    let remove_rightmost t = Option.map (remove_rightmost' t) ~f:fst

    let rec find_and_remove_leftmost' t =
      match t with
      | Leaf1 elt -> (elt, None)
      | Leaf2 (elt1, elt2) -> (elt1, Some (Leaf1 elt2, Height_decreased))
      | Two (left, elt, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (two_left_maybe_shrank left_opt elt right))
      | OneTwo (left, elt, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (one_two_left_maybe_shrank left_opt elt right))
      | TwoOne (left, elt, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (two_one_left_maybe_shrank left_opt elt right))
    ;;

    let find_and_remove_leftmost t =
      let (leftmost, t) = find_and_remove_leftmost' t in
      (leftmost, Option.map t ~f:fst)
    ;;

    let rec find_and_remove_rightmost' t =
      match t with
      | Leaf1 elt -> (elt, None)
      | Leaf2 (elt1, elt2) -> (elt2, Some (Leaf1 elt1, Height_decreased))
      | Two (left, elt, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (two_right_maybe_shrank left elt right_opt))
      | OneTwo (left, elt, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (one_two_right_maybe_shrank left elt right_opt))
      | TwoOne (left, elt, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (two_one_right_maybe_shrank left elt right_opt))
    ;;

    let find_and_remove_rightmost t =
      let (rightmost, t) = find_and_remove_rightmost' t in
      (rightmost, Option.map t ~f:fst)
    ;;

    (* requires [height_difference = height left - height right] and [height_difference >= 0] *)
    let rec join_into_left left elt right ~height_difference =
      match height_difference with
      | 0 -> (Two (left, elt, right), Height_increased)
      | 1 -> (TwoOne (left, elt, right), Height_increased)
      | _ ->
        match left with
        | Leaf1 _ | Leaf2 _ -> assert false
        | Two (left_left, elt', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right elt right ~height_difference:(height_difference - 1)
          in
          two_right_maybe_grew left_left elt' (left_right, height_increased)
        | OneTwo (left_left, elt', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right elt right ~height_difference:(height_difference - 1)
          in
          one_two_right_maybe_grew left_left elt' (left_right, height_increased)
        | TwoOne (left_left, elt', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right elt right ~height_difference:(height_difference - 2)
          in
          two_one_right_maybe_grew left_left elt' (left_right, height_increased)
    ;;

    (* requires [height_difference = height right - height left] and [height_difference >= 0] *)
    let rec join_into_right left elt right ~height_difference =
      match height_difference with
      | 0 -> (Two (left, elt, right), Height_increased)
      | 1 -> (OneTwo (left, elt, right), Height_increased)
      | _ ->
        match right with
        | Leaf1 _ | Leaf2 _ -> assert false
        | Two (right_left, elt', right_right) ->
          let (right_left, height_increased) =
            join_into_right left elt right_left ~height_difference:(height_difference - 1)
          in
          two_left_maybe_grew (right_left, height_increased) elt' right_right
        | OneTwo (right_left, elt', right_right) ->
          let (right_left, height_increased) =
            join_into_right left elt right_left ~height_difference:(height_difference - 2)
          in
          one_two_left_maybe_grew (right_left, height_increased) elt' right_right
        | TwoOne (right_left, elt', right_right) ->
          let (right_left, height_increased) =
            join_into_right left elt right_left ~height_difference:(height_difference - 1)
          in
          two_one_left_maybe_grew (right_left, height_increased) elt' right_right
    ;;

    (* CR wduff: Expose join in the interface and move it to the "balanced" section. *)
    let join left left_height elt right right_height =
      if left_height > right_height
      then begin
        let (t, height_increased) =
          join_into_left left elt right ~height_difference:(left_height - right_height)
        in
        (t, left_height + Height_increase.to_int height_increased)
      end
      else
        let (t, height_increased) =
          join_into_right left elt right ~height_difference:(right_height - left_height)
        in
        (t, right_height + Height_increase.to_int height_increased)
    ;;

    let join0 left left_height right right_height =
      match Ordering.of_int (Int.compare left_height right_height) with
      | Less ->
        let (elt, right_opt) = find_and_remove_leftmost' right in
        let (right, height_decreased) = Option.value_exn right_opt in
        let (t, height_increased) =
          join_into_right left elt right ~height_difference:(right_height - left_height)
        in
        let height = right_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased in
        (t, height)
      | Equal ->
        let (elt, right_opt) = find_and_remove_leftmost' right in
        let (t, height_decreased) = two_right_maybe_shrank left elt right_opt in
        (t, left_height + 1 - Height_decrease.to_int height_decreased)
      | Greater ->
        let (elt, left_opt) = find_and_remove_rightmost' left in
        let (left, height_decreased) = Option.value_exn left_opt in
        let (t, height_increased) =
          join_into_left left elt right ~height_difference:(left_height - right_height)
        in
        let height = left_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased in
        (t, height)
    ;;

    let rec of_raw_tree' raw_tree =
      match raw_tree with
      | Leaf1 _ -> raw_tree, 1
      | Leaf2 _ -> raw_tree, 2
      | Two (left, elt, right) | OneTwo (left, elt, right) | TwoOne (left, elt, right) ->
        let (left, left_height) = of_raw_tree' left in
        let (right, right_height) = of_raw_tree' right in
        join left left_height elt right right_height
    ;;

    let of_raw_tree raw_tree =
      let (t, _height) = of_raw_tree' raw_tree in
      t
    ;;
  end

  let height t =
    match t with
    | None -> 0
    | Some non_empty -> Non_empty.height non_empty
  ;;

  let of_raw_tree raw_tree =
    match raw_tree with
    | None -> None
    | Some non_empty_raw_tree -> Some (Non_empty.of_raw_tree non_empty_raw_tree)
  ;;

  let of_balanced_raw_tree_unchecked raw_tree = raw_tree

  let of_balanced_raw_tree_exn raw_tree =
    match raw_tree with
    | None -> None
    | Some non_empty_raw_tree ->
      Some (Non_empty.of_balanced_raw_tree_exn non_empty_raw_tree)
  ;;

  let to_raw_tree t = t

  let remove_leftmost t =
    Option.bind t ~f:Non_empty.remove_leftmost
  ;;

  let remove_leftmost' t =
    match t with
    | None -> (None, Height_unchanged)
    | Some non_empty ->
      match Non_empty.remove_leftmost' non_empty with
      | None -> (None, Height_decreased)
      | Some (non_empty, height_decreased) -> (Some non_empty, height_decreased)
  ;;

  let remove_rightmost t =
    Option.bind t ~f:Non_empty.remove_rightmost
  ;;

  let remove_rightmost' t =
    match t with
    | None -> (None, Height_unchanged)
    | Some non_empty ->
      match Non_empty.remove_rightmost' non_empty with
      | None -> (None, Height_decreased)
      | Some (non_empty, height_decreased) -> (Some non_empty, height_decreased)
  ;;

  let find_and_remove_leftmost t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (leftmost, t) = Non_empty.find_and_remove_leftmost non_empty in
      (Some leftmost, t)
  ;;

  let find_and_remove_leftmost' t =
    match t with
    | None -> (None, t, Height_unchanged)
    | Some non_empty ->
      let (leftmost, opt) = Non_empty.find_and_remove_leftmost' non_empty in
      let (t, height_decreased) =
        match opt with
        | None -> (None, Height_decreased)
        | Some (non_empty, height_decreased) -> (Some non_empty, height_decreased)
      in
      (Some leftmost, t, height_decreased)
  ;;

  let find_and_remove_rightmost t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (rightmost, t) = Non_empty.find_and_remove_rightmost non_empty in
      (Some rightmost, t)
  ;;

  let find_and_remove_rightmost' t =
    match t with
    | None -> (None, t, Height_unchanged)
    | Some non_empty ->
      let (leftmost, opt) = Non_empty.find_and_remove_rightmost' non_empty in
      let (t, height_decreased) =
        match opt with
        | None -> (None, Height_decreased)
        | Some (non_empty, height_decreased) -> (Some non_empty, height_decreased)
      in
      (Some leftmost, t, height_decreased)
  ;;
end

module Balanced_tree2(* : Balanced_tree2
  with type 'a tree1 := 'a Balanced_tree.t
  with type 'a non_empty_tree1 := 'a Balanced_tree.Non_empty.t
  with type ('a, 'b) raw_tree := ('a, 'b) Tree2.t
  with type ('a, 'b) non_empty_raw_tree := ('a, 'b) Tree2.Non_empty.t
  with type ('a, 'b) t = ('a, 'b) Tree2.t
  with type ('a, 'b) Non_empty.t = ('a, 'b) Tree2.Non_empty.t *)=
struct
  include (Tree2 : module type of struct include Tree2 end with module Non_empty := Tree2.Non_empty)

  module Non_empty(* : Non_empty_balanced_tree2
    with type 'a tree1 := 'a Balanced_tree.Non_empty.t
    with type ('a, 'b) raw_tree := ('a, 'b) Tree2.Non_empty.t
    with type ('a, 'b) maybe_empty := ('a, 'b) t
    with type ('a, 'b) t = ('a, 'b) Tree2.Non_empty.t *)=
  struct
    include Tree2.Non_empty

    (* CR wduff: Insert invariant checks around toplevel functions controlled by a debug flag. *)
    let rec height_invariant t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (left, _, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        assert (left_height = right_height);
        left_height + 1
      | OneTwo (left, _, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        assert (left_height + 1 = right_height);
        right_height + 1
      | TwoOne (left, _, _, right) ->
        let left_height = height_invariant left in
        let right_height = height_invariant right in
        if not (left_height = right_height + 1) then raise_s [%message "" (t : (_, _) t)(Backtrace.get() : Backtrace.t)];
        left_height + 1
    ;;

    let of_balanced_raw_tree_unchecked raw_tree = raw_tree

    let of_balanced_raw_tree_exn raw_tree =
      ignore (height_invariant raw_tree : int);
      of_balanced_raw_tree_unchecked raw_tree
    ;;

    let to_raw_tree t = t

    let rec height t =
      match t with
      | Leaf1 _ -> 1
      | Leaf2 _ -> 2
      | Two (_, _, _, right) -> height right + 1
      | OneTwo (left, _, _, _) -> height left + 2
      | TwoOne (_, _, _, right) -> height right + 2
    ;;

    let rebalance_left_is_2_shorter' left a b right =
      match right with
      | Leaf1 _ | Leaf2 _ | Two _ ->
        (* Since left is a [Non_empty.t], [height left >= 1], so since
           [height right = height left + 2], [height right >= 3].
           Further, a height increase can never result in a [Two] node. *)
        assert false
      | OneTwo (right_left, a', b', right_right) ->
        Two (Two (left, a, b, right_left), a', b', right_right)
      | TwoOne (right_left, a', b', right_right) ->
        match right_left with
        | Leaf1 _ ->
          (* Since [height right >= 3], [height right_left >= 2]. *)
          assert false
        | Leaf2 (a1, b1, a2, b2) ->
          (match right_right with
           | Leaf1 (a'', b'') ->
             Two (Two (left, a, b, Leaf1 (a1, b1)), a2, b2, Leaf2 (a', b', a'', b''))
           | _ ->
             (* Since [height right_left = 2], [height right_right = 1]. *)
             assert false)
        | Two (right_left_left, a'', b'', right_left_right) ->
          Two
            (Two (left, a, b, right_left_left),
             a'', b'',
             Two (right_left_right, a', b', right_right))
        | OneTwo (right_left_left, a'', b'', right_left_right) ->
          Two
            (TwoOne (left, a, b, right_left_left),
             a'', b'',
             Two (right_left_right, a', b', right_right))
        | TwoOne (right_left_left, a'', b'', right_left_right) ->
          Two
            (Two (left, a, b, right_left_left),
             a'', b'',
             OneTwo (right_left_right, a', b', right_right))
    ;;

    let rebalance_left_is_2_shorter left a b right =
      match right with
      | Two (right_left, a', b', right_right) ->
        (TwoOne (OneTwo (left, a, b, right_left), a', b', right_right), Height_unchanged)
      | _ ->
        (rebalance_left_is_2_shorter' left a b right, Height_decreased)
    ;;

    let rebalance_right_is_2_shorter' left a b right =
      match left with
      | Leaf1 _ | Leaf2 _ | Two _ ->
        (* Since right is a [Non_empty.t], [height right >= 1], so since
           [height left = height right + 2], [height left >= 3].
           Further, a height increase can never result in a [Two] node. *)
        assert false
      | TwoOne (left_left, a', b', left_right) ->
        Two (left_left, a', b', Two (left_right, a, b, right))
      | OneTwo (left_left, a', b', left_right) ->
        match left_right with
        | Leaf1 _ ->
          (* Since [height left >= 3], [height left_right >= 2]. *)
          assert false
        | Leaf2 (a1, b1, a2, b2) ->
          (match left_left with
           | Leaf1 (a'', b'') ->
             Two (Leaf2 (a'', b'', a', b'), a1, b1, Two (Leaf1 (a2, b2), a, b, right))
           | _ ->
             (* Since [height left_right = 2], [height left_left = 1]. *)
             assert false)
        | Two (left_right_left, a'', b'', left_right_right) ->
          Two
            (Two (left_left, a', b', left_right_left),
             a'', b'',
             Two (left_right_right, a, b, right))
        | OneTwo (left_right_left, a'', b'', left_right_right) ->
          Two
            (TwoOne (left_left, a', b', left_right_left),
             a'', b'',
             Two (left_right_right, a, b, right))
        | TwoOne (left_right_left, a'', b'', left_right_right) ->
          Two
            (Two (left_left, a', b', left_right_left),
             a'', b'',
             OneTwo (left_right_right, a, b, right))
    ;;

    let rebalance_right_is_2_shorter left a b right =
      match left with
      | Two (left_left, a', b', left_right) ->
        (OneTwo (left_left, a', b', TwoOne (left_right, a, b, right)), Height_unchanged)
      | _ ->
        (rebalance_right_is_2_shorter' left a b right, Height_decreased)
    ;;

    let two_left_maybe_grew (left, height_increased) a b right : _ * Height_increase.t =
      match (height_increased : Height_increase.t) with
      | Height_unchanged ->
        (Two (left, a, b, right), Height_unchanged)
      | Height_increased ->
        (TwoOne (left, a, b, right), Height_increased)
    ;;

    let one_two_left_maybe_grew (left, height_increased) a b right : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged ->
          OneTwo (left, a, b, right)
        | Height_increased ->
          Two (left, a, b, right)
      in
      (t, Height_unchanged)
    ;;

    let two_one_left_maybe_grew (left, height_increased) a b right : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged ->
          TwoOne (left, a, b, right)
        | Height_increased ->
          rebalance_right_is_2_shorter' left a b right
      in
      (t, Height_unchanged)
    ;;

    let two_right_maybe_grew left a b (right, height_increased) : _ * Height_increase.t =
      match (height_increased : Height_increase.t) with
      | Height_unchanged ->
        (Two (left, a, b, right), Height_unchanged)
      | Height_increased ->
        (OneTwo (left, a, b, right), Height_increased)
    ;;

    let one_two_right_maybe_grew left a b (right, height_increased) : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged ->
          OneTwo (left, a, b, right)
        | Height_increased ->
          rebalance_left_is_2_shorter' left a b right
      in
      (t, Height_unchanged)
    ;;

    let two_one_right_maybe_grew left a b (right, height_increased) : _ * Height_increase.t =
      let t =
        match (height_increased : Height_increase.t) with
        | Height_unchanged ->
          TwoOne (left, a, b, right)
        | Height_increased ->
          Two (left, a, b, right)
      in
      (t, Height_unchanged)
    ;;

    let two_left_maybe_shrank left_opt a b right =
      let t =
        match left_opt with
        | None ->
          (match right with
           | Leaf1 (a', b') -> Leaf2 (a, b, a', b')
           | _ -> assert false)
        | Some (left, height_decreased) ->
          match height_decreased with
          | Height_unchanged ->
            Two (left, a, b, right)
          | Height_decreased ->
            OneTwo (left, a, b, right)
      in
      (t, Height_unchanged)
    ;;

    let one_two_left_maybe_shrank left_opt a b right =
      match left_opt with
      | None ->
        (match right with
         | Leaf2 (a1, b1, a2, b2) ->
           (Two (Leaf1 (a, b), a1, b1, Leaf1 (a2, b2)), Height_decreased)
         | Two (Leaf1 (a1, b1), a2, b2, right_right) ->
           (TwoOne (Leaf2 (a, b, a1, b1), a2, b2, right_right), Height_unchanged)
         | _ -> assert false)
      | Some (left, height_decreased) ->
        match height_decreased with
        | Height_unchanged ->
          (OneTwo (left, a, b, right), Height_unchanged)
        | Height_decreased ->
          rebalance_left_is_2_shorter left a b right
    ;;

    let two_one_left_maybe_shrank left_opt a b right =
      match left_opt with
      | None -> assert false
      | Some (left, height_decreased) ->
        match height_decreased with
        | Height_unchanged ->
          (TwoOne (left, a, b, right), Height_unchanged)
        | Height_decreased ->
          (Two (left, a, b, right), Height_decreased)
    ;;

    let two_right_maybe_shrank left a b right_opt =
      let t =
        match right_opt with
        | None ->
          (match left with
           | Leaf1 (a', b') -> Leaf2 (a, b, a', b')
           | _ -> assert false)
        | Some (right, height_decreased) ->
          match height_decreased with
          | Height_unchanged ->
            Two (left, a, b, right)
          | Height_decreased ->
            TwoOne (left, a, b, right)
      in
      (t, Height_unchanged)
    ;;

    let one_two_right_maybe_shrank left a b right_opt =
      match right_opt with
      | None -> assert false
      | Some (right, height_decreased) ->
        match height_decreased with
        | Height_unchanged ->
          (OneTwo (left, a, b, right), Height_unchanged)
        | Height_decreased ->
          (Two (left, a, b, right), Height_decreased)
    ;;

    let two_one_right_maybe_shrank left a b right_opt =
      match right_opt with
      | None ->
        (match left with
         | Leaf2 (a1, b1, a2, b2) ->
           (Two (Leaf1 (a1, b1), a2, b2, Leaf1 (a, b)), Height_decreased)
         | Two (Leaf1 (a1, b1), a2, b2, right_right) ->
           (TwoOne (Leaf2 (a1, b1, a2, b2), a, b, right_right), Height_unchanged)
         | _ -> assert false)
      | Some (right, height_decreased) ->
        match height_decreased with
        | Height_unchanged ->
          (TwoOne (left, a, b, right), Height_unchanged)
        | Height_decreased ->
          rebalance_right_is_2_shorter left a b right
    ;;

    let rec remove_leftmost' t =
      match t with
      | Leaf1 (_, _) -> None
      | Leaf2 (_, _, a2, b2) -> Some (Leaf1 (a2, b2), Height_decreased)
      | Two (left, a, b, right) ->
        Some (two_left_maybe_shrank (remove_leftmost' left) a b right)
      | OneTwo (left, a, b, right) ->
        Some (one_two_left_maybe_shrank (remove_leftmost' left) a b right)
      | TwoOne (left, a, b, right) ->
        Some (two_one_left_maybe_shrank (remove_leftmost' left) a b right)
    ;;

    let remove_leftmost t = Option.map (remove_leftmost' t) ~f:fst

    let rec remove_rightmost' t =
      match t with
      | Leaf1 (_, _) -> None
      | Leaf2 (a1, b1, _, _) -> Some (Leaf1 (a1, b1), Height_decreased)
      | Two (left, a, b, right) ->
        Some (two_right_maybe_shrank left a b (remove_rightmost' right))
      | OneTwo (left, a, b, right) ->
        Some (one_two_right_maybe_shrank left a b (remove_rightmost' right))
      | TwoOne (left, a, b, right) ->
        Some (two_one_right_maybe_shrank left a b (remove_rightmost' right))
    ;;

    let remove_rightmost t = Option.map (remove_rightmost' t) ~f:fst

    let rec find_and_remove_leftmost' t =
      match t with
      | Leaf1 (a, b) -> ((a, b), None)
      | Leaf2 (a1, b1, a2, b2) -> ((a1, b1), Some (Leaf1 (a2, b2), Height_decreased))
      | Two (left, a, b, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (two_left_maybe_shrank left_opt a b right))
      | OneTwo (left, a, b, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (one_two_left_maybe_shrank left_opt a b right))
      | TwoOne (left, a, b, right) ->
        let (min, left_opt) = find_and_remove_leftmost' left in
        (min, Some (two_one_left_maybe_shrank left_opt a b right))
    ;;

    let find_and_remove_leftmost t =
      let (leftmost, t) = find_and_remove_leftmost' t in
      (leftmost, Option.map t ~f:fst)
    ;;

    let rec find_and_remove_rightmost' t =
      match t with
      | Leaf1 (a, b) -> ((a, b), None)
      | Leaf2 (a1, b1, a2, b2) -> ((a2, b2), Some (Leaf1 (a1, b1), Height_decreased))
      | Two (left, a, b, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (two_right_maybe_shrank left a b right_opt))
      | OneTwo (left, a, b, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (one_two_right_maybe_shrank left a b right_opt))
      | TwoOne (left, a, b, right) ->
        let (max, right_opt) = find_and_remove_rightmost' right in
        (max, Some (two_one_right_maybe_shrank left a b right_opt))
    ;;

    let find_and_remove_rightmost t =
      let (rightmost, t) = find_and_remove_rightmost' t in
      (rightmost, Option.map t ~f:fst)
    ;;

    (* requires [height_difference = height left - height right] and [height_difference >= 0] *)
    let rec join_into_left left a b right ~height_difference =
      match height_difference with
      | 0 -> (Two (left, a, b, right), Height_increased)
      | 1 -> (TwoOne (left, a, b, right), Height_increased)
      | _ ->
        match left with
        | Leaf1 _ | Leaf2 _ -> assert false
        | Two (left_left, a', b', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right a b right ~height_difference:(height_difference - 1)
          in
          two_right_maybe_grew left_left a' b' (left_right, height_increased)
        | OneTwo (left_left, a', b', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right a b right ~height_difference:(height_difference - 1)
          in
          one_two_right_maybe_grew left_left a' b' (left_right, height_increased)
        | TwoOne (left_left, a', b', left_right) ->
          let (left_right, height_increased) =
            join_into_left left_right a b right ~height_difference:(height_difference - 2)
          in
          two_one_right_maybe_grew left_left a' b' (left_right, height_increased)
    ;;

    (* requires [height_difference = height right - height left] and [height_difference >= 0] *)
    let rec join_into_right left a b right ~height_difference =
      match height_difference with
      | 0 -> (Two (left, a, b, right), Height_increased)
      | 1 -> (OneTwo (left, a, b, right), Height_increased)
      | _ ->
        match right with
        | Leaf1 _ | Leaf2 _ -> assert false
        | Two (right_left, a', b', right_right) ->
          let (right_left, height_increased) =
            join_into_right left a b right_left ~height_difference:(height_difference - 1)
          in
          two_left_maybe_grew (right_left, height_increased) a' b' right_right
        | OneTwo (right_left, a', b', right_right) ->
          let (right_left, height_increased) =
            join_into_right left a b right_left ~height_difference:(height_difference - 2)
          in
          one_two_left_maybe_grew (right_left, height_increased) a' b' right_right
        | TwoOne (right_left, a', b', right_right) ->
          let (right_left, height_increased) =
            join_into_right left a b right_left ~height_difference:(height_difference - 1)
          in
          two_one_left_maybe_grew (right_left, height_increased) a' b' right_right
    ;;

    let join left left_height a b right right_height =
      if left_height > right_height
      then begin
        let (t, height_increased) =
          join_into_left left a b right ~height_difference:(left_height - right_height)
        in
        (t, left_height + Height_increase.to_int height_increased)
      end
      else
        let (t, height_increased) =
          join_into_right left a b right ~height_difference:(right_height - left_height)
        in
        (t, right_height + Height_increase.to_int height_increased)
    ;;

    let join0 left left_height right right_height =
      match Ordering.of_int (Int.compare left_height right_height) with
      | Less ->
        let ((a, b), right_opt) = find_and_remove_leftmost' right in
        let (right, height_decreased) = Option.value_exn right_opt in
        let (t, height_increased) =
          join_into_right left a b right ~height_difference:(right_height - left_height)
        in
        let height = right_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased in
        (t, height)
      | Equal ->
        let ((a, b), right_opt) = find_and_remove_leftmost' right in
        let (t, height_decreased) = two_right_maybe_shrank left a b right_opt in
        (t, left_height + 1 - Height_decrease.to_int height_decreased)
      | Greater ->
        let ((a, b), left_opt) = find_and_remove_rightmost' left in
        let (left, height_decreased) = Option.value_exn left_opt in
        let (t, height_increased) =
          join_into_left left a b right ~height_difference:(left_height - right_height)
        in
        let height = left_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased in
        (t, height)
    ;;

    let rec of_raw_tree' raw_tree =
      match raw_tree with
      | Leaf1 _ -> raw_tree, 1
      | Leaf2 _ -> raw_tree, 2
      | Two (left, key, data, right)
      | OneTwo (left, key, data, right)
      | TwoOne (left, key, data, right)
        ->
        let (left, left_height) = of_raw_tree' left in
        let (right, right_height) = of_raw_tree' right in
        join left left_height key data right right_height
    ;;

    let of_raw_tree raw_tree =
      let (t, _height) = of_raw_tree' raw_tree in
      t
    ;;
  end

  let height t =
    match t with
    | None -> 0
    | Some non_empty -> Non_empty.height non_empty
  ;;

  let of_raw_tree raw_tree =
    match raw_tree with
    | None -> None
    | Some non_empty_raw_tree -> Some (Non_empty.of_raw_tree non_empty_raw_tree)
  ;;

  let of_balanced_raw_tree_unchecked raw_tree = raw_tree

  let of_balanced_raw_tree_exn raw_tree =
    match raw_tree with
    | None -> None
    | Some non_empty_raw_tree ->
      Some (Non_empty.of_balanced_raw_tree_exn non_empty_raw_tree)
  ;;

  let to_raw_tree t = t

  let remove_leftmost t =
    Option.bind t ~f:Non_empty.remove_leftmost
  ;;

  let remove_rightmost t =
    Option.bind t ~f:Non_empty.remove_rightmost
  ;;

  let find_and_remove_leftmost t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (leftmost, t) = Non_empty.find_and_remove_leftmost non_empty in
      (Some leftmost, t)
  ;;

  let find_and_remove_rightmost t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (rightmost, t) = Non_empty.find_and_remove_rightmost non_empty in
      (Some rightmost, t)
  ;;
end

let convert_compare = Compare.convert
let do_compare = Compare.do_compare

(* CR wduff: Better error messages. *)
let check_less elt1 elt2 ~compare =
  match do_compare compare elt1 elt2 with
  | Less -> ()
  | Equal -> raise_s [%message "duplicate element"]
  | Greater -> raise_s [%message "elements out of order"]
;;

module Set = struct
  module Non_empty : Non_empty_set
    with type 'a balanced_tree := 'a Balanced_tree.Non_empty.t
    with type ('a, 'cmp) maybe_empty := 'a Balanced_tree.t
    with type ('a, 'cmp) t = 'a Balanced_tree.Non_empty.t =
  struct
    module Balanced_tree = Balanced_tree.Non_empty
    (* CR wduff: Eww. *)
    open Tree.Non_empty

    type ('a, 'cmp) t = 'a Balanced_tree.t [@@deriving sexp_of]

    let rec check_sorted'' t ~left_max ~compare =
      match t with
      | Leaf1 elt ->
        check_less left_max elt ~compare;
        elt
      | Leaf2 (elt1, elt2) ->
        check_less left_max elt1 ~compare;
        check_less elt1 elt2 ~compare;
        elt2
      | Two (left, elt, right) | OneTwo (left, elt, right) | TwoOne (left, elt, right) ->
        let left_max = check_sorted'' left ~left_max ~compare in
        check_less left_max elt ~compare;
        check_sorted'' right ~left_max:elt ~compare

    let rec check_sorted' t ~compare =
      match t with
      | Leaf1 elt -> elt
      | Leaf2 (elt1, elt2) ->
        check_less elt1 elt2 ~compare;
        elt2
      | Two (left, elt, right) | OneTwo (left, elt, right) | TwoOne (left, elt, right) ->
        let left_max = check_sorted' left ~compare in
        check_less left_max elt ~compare;
        check_sorted'' right ~left_max:elt ~compare
    ;;

    (* CR wduff: Consider checking this in debug mode. *)
    let check_sorted (t : ('a, 'cmp) t) ~compare =
      ignore (check_sorted' t ~compare : 'a)
    ;;

    let height = Balanced_tree.height
    let length = Balanced_tree.length
    let singleton = Balanced_tree.singleton
    let of_sorted_array_unchecked = Balanced_tree.of_array
    let of_sorted_list_unchecked = Balanced_tree.of_list
    let to_list = Balanced_tree.to_list
    let iter = Balanced_tree.iter
    let fold = Balanced_tree.fold
    let fold_right = Balanced_tree.fold_right
    let find_min = Balanced_tree.find_leftmost
    let find_max = Balanced_tree.find_rightmost
    let two_left_maybe_grew = Balanced_tree.two_left_maybe_grew
    let one_two_left_maybe_grew = Balanced_tree.one_two_left_maybe_grew
    let two_one_left_maybe_grew = Balanced_tree.two_one_left_maybe_grew
    let two_right_maybe_grew = Balanced_tree.two_right_maybe_grew
    let one_two_right_maybe_grew = Balanced_tree.one_two_right_maybe_grew
    let two_one_right_maybe_grew = Balanced_tree.two_one_right_maybe_grew
    let two_left_maybe_shrank = Balanced_tree.two_left_maybe_shrank
    let one_two_left_maybe_shrank = Balanced_tree.one_two_left_maybe_shrank
    let two_one_left_maybe_shrank = Balanced_tree.two_one_left_maybe_shrank
    let two_right_maybe_shrank = Balanced_tree.two_right_maybe_shrank
    let one_two_right_maybe_shrank = Balanced_tree.one_two_right_maybe_shrank
    let two_one_right_maybe_shrank = Balanced_tree.two_one_right_maybe_shrank
    let remove_min = Balanced_tree.remove_leftmost
    let remove_max = Balanced_tree.remove_rightmost
    let find_and_remove_min' = Balanced_tree.find_and_remove_leftmost'
    let find_and_remove_min = Balanced_tree.find_and_remove_leftmost
    let find_and_remove_max' = Balanced_tree.find_and_remove_rightmost'
    let find_and_remove_max = Balanced_tree.find_and_remove_rightmost
    let join_into_left = Balanced_tree.join_into_left
    let join_into_right = Balanced_tree.join_into_right
    let join = Balanced_tree.join
    let join0 = Balanced_tree.join0

    let resorting_map t ~f ~compare =
      let array =
        List.to_array (to_list t)
        |> Array.map ~f
      in
      Array.sort array ~compare:(convert_compare compare);
      of_sorted_array_unchecked array
    ;;

    let of_sorted_balanced_tree_unchecked balanced_tree = balanced_tree

    let of_sorted_balanced_tree_exn balanced_tree ~compare =
      check_sorted balanced_tree ~compare;
      of_sorted_balanced_tree_unchecked balanced_tree
    ;;

    let to_balanced_tree t = t

    let of_sorted_array_exn array ~compare =
      if Array.is_sorted array ~compare:(convert_compare compare)
      then of_sorted_array_unchecked array
      else
        (* CR wduff: *)
        raise_s [%message]
    ;;

    let of_array array ~compare =
      let copy = Array.copy array in
      Array.sort copy ~compare:(convert_compare compare);
      of_sorted_array_unchecked copy
    ;;

    let of_sorted_list_exn list ~compare =
      if List.is_sorted list ~compare:(convert_compare compare)
      then of_sorted_list_unchecked list
      else
        (* CR wduff: *)
        raise_s [%message]
    ;;

    let of_list list ~compare =
      let array = Array.of_list list in
      Array.sort array ~compare:(convert_compare compare);
      of_sorted_array_unchecked array
    ;;

    (* CR wduff: Expose this? *)
    let rec mem t elt ~compare =
      match t with
      | Leaf1 elt' ->
        (match do_compare compare elt elt' with
         | Equal -> true
         | Less | Greater -> false)
      | Leaf2 (elt1, elt2) ->
        (match do_compare compare elt elt1 with
         | Equal -> true
         | Less | Greater ->
           match do_compare compare elt elt2 with
           | Equal -> true
           | Less | Greater -> false)
      | Two (left, elt', right)
      | OneTwo (left, elt', right)
      | TwoOne (left, elt', right)
        ->
        match do_compare compare elt elt' with
        | Less -> mem left elt ~compare
        | Equal -> true
        | Greater -> mem right elt ~compare
    ;;

    let rec generic_add' t elt ~on_already_present ~compare =
      match t with
      | Leaf1 elt' ->
        (match do_compare compare elt elt' with
         | Less -> (Leaf2 (elt, elt'), Height_increased)
         | Equal ->
           on_already_present elt;
           (t, Height_unchanged)
         | Greater -> (Leaf2 (elt', elt), Height_increased))
      | Leaf2 (elt1, elt2) ->
        let t =
          (match do_compare compare elt elt1 with
           | Less -> Two (Leaf1 elt, elt1, Leaf1 elt2)
           | Equal ->
             on_already_present elt;
             t
           | Greater ->
             match do_compare compare elt elt2 with
             | Less -> Two (Leaf1 elt1, elt, Leaf1 elt2)
             | Equal ->
               on_already_present elt;
               t
             | Greater -> Two (Leaf1 elt1, elt2, Leaf1 elt))
        in
        (t, Height_unchanged)
      | Two (left, elt', right) ->
        (match do_compare compare elt elt' with
         | Less ->
           let (left, height_increased) =
             generic_add' left elt ~on_already_present ~compare
           in
           two_left_maybe_grew (left, height_increased) elt right
         | Equal ->
           on_already_present elt;
           (t, Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right elt ~on_already_present ~compare
           in
           two_right_maybe_grew left elt (right, height_increased))
      | OneTwo (left, elt', right) ->
        (match do_compare compare elt elt' with
         | Less ->
           let (left, height_increased) =
             generic_add' left elt ~on_already_present ~compare
           in
           one_two_left_maybe_grew (left, height_increased) elt right
         | Equal ->
           on_already_present elt;
           (t, Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right elt ~on_already_present ~compare
           in
           one_two_right_maybe_grew left elt (right, height_increased))
      | TwoOne (left, elt', right) ->
        (match do_compare compare elt elt' with
         | Less ->
           let (left, height_increased) =
             generic_add' left elt ~on_already_present ~compare
           in
           two_one_left_maybe_grew (left, height_increased) elt right
         | Equal ->
           on_already_present elt;
           (t, Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right elt ~on_already_present ~compare
           in
           two_one_right_maybe_grew left elt (right, height_increased))
    ;;

    let generic_add t elt ~on_already_present ~compare =
      let (t, _height_increased) = generic_add' t elt ~on_already_present ~compare in
      t
    ;;

    let add' t elt ~compare =
      let on_already_present _ = () in
      generic_add' t elt ~on_already_present ~compare
    ;;

    (* CR wduff: Should this use add' instead? *)
    let add t elt ~compare =
      let on_already_present _ = () in
      generic_add t elt ~on_already_present ~compare
    ;;

    let strict_add_exn t elt ~compare =
      (* CR wduff: Better error and/or faster error. *)
      let on_already_present _ = raise_s [%message] in
      generic_add t elt ~compare ~on_already_present
    ;;

    let strict_add t elt ~compare =
      match strict_add_exn t elt ~compare with
      | t -> `Ok t
      | exception _ -> `Duplicate_elt
    ;;

    (* CR wduff: Special case unchanged so that we don't have to rebuild the spine? *)
    let rec generic_remove' t elt ~on_not_present ~compare =
      match t with
      | Leaf1 elt' ->
        (match do_compare compare elt elt' with
         | Equal -> None
         | Less | Greater ->
           on_not_present ();
           Some (t, Height_unchanged))
      | Leaf2 (elt1, elt2) ->
        (match do_compare compare elt elt1 with
         | Equal -> Some (Leaf1 elt2, Height_decreased)
         | Less | Greater ->
           match do_compare compare elt elt2 with
           | Equal -> Some (Leaf1 elt1, Height_decreased)
           | Less | Greater ->
             on_not_present ();
             Some (t, Height_unchanged))
      | Two (left, elt', right) ->
        let t_with_height_decreased =
          match do_compare compare elt elt' with
          | Less ->
            let left_opt = generic_remove' left elt ~on_not_present ~compare in
            two_left_maybe_shrank left_opt elt' right
          | Equal ->
            let (right_min_elt, right_opt) = find_and_remove_min' right in
            two_right_maybe_shrank left right_min_elt right_opt
          | Greater ->
            let right_opt = generic_remove' right elt ~on_not_present ~compare in
            two_right_maybe_shrank left elt' right_opt
        in
        Some t_with_height_decreased
      | OneTwo (left, elt', right) ->
        let t_with_height_decreased =
          match do_compare compare elt elt' with
          | Less ->
            let left_opt = generic_remove' left elt ~on_not_present ~compare in
            one_two_left_maybe_shrank left_opt elt' right
          | Equal ->
            let (right_min_elt, right_opt) =
              find_and_remove_min' right
            in
            one_two_right_maybe_shrank left right_min_elt right_opt
          | Greater ->
            let right_opt = generic_remove' right elt ~on_not_present ~compare in
            one_two_right_maybe_shrank left elt' right_opt
        in
        Some t_with_height_decreased
      | TwoOne (left, elt', right) ->
        let t_with_height_decreased =
          match do_compare compare elt elt' with
          | Less ->
            let left_opt = generic_remove' left elt ~on_not_present ~compare in
            two_one_left_maybe_shrank left_opt elt' right
          | Equal ->
            let (left_max_elt, left_opt) =
              find_and_remove_max' left
            in
            two_one_left_maybe_shrank left_opt left_max_elt right
          | Greater ->
            let right_opt = generic_remove' right elt ~on_not_present ~compare in
            two_one_right_maybe_shrank left elt' right_opt
        in
        Some t_with_height_decreased
    ;;

    let generic_remove t elt ~on_not_present ~compare =
      match generic_remove' t elt ~on_not_present ~compare with
      | None -> None
      | Some (t, _height_decreased) -> Some t
    ;;

    let remove' t elt ~compare =
      generic_remove' t elt ~on_not_present:(fun () -> ()) ~compare

    let remove t elt ~compare =
      generic_remove t elt ~on_not_present:(fun () -> ()) ~compare
    ;;

    let strict_remove_exn t elt ~compare =
      (* CR wduff: Better error and/or faster error. *)
      generic_remove t elt ~on_not_present:(fun () -> raise_s [%message]) ~compare
    ;;

    let strict_remove t elt ~compare =
      match strict_remove_exn t elt ~compare with
      | t -> `Ok t
      | exception _ -> `Not_found
    ;;

    (* CR wduff: This is wrong. See [Map.split]. At the very least, it gets the height wrong in the
       "-1" cases, and drops the current element in the "None" cases. *)
    let rec split t elt ~compare =
      match t with
      | Leaf1 elt' ->
        (match do_compare compare elt elt' with
         | Less -> (None, 1, false, Some t, 0)
         | Equal -> (None, 1, true, None, 1)
         | Greater -> (Some t, 0, false, None, 1))
      | Leaf2 (elt1, elt2) ->
        (match do_compare compare elt elt1 with
         | Less -> (None, 2, false, Some t, 0)
         | Equal -> (None, 2, true, Some (Leaf1 elt2), 1)
         | Greater ->
           match do_compare compare elt elt2 with
           | Less -> (Some (Leaf1 elt1), 1, false, Some (Leaf1 elt2), 1)
           | Equal -> (Some (Leaf1 elt1), 1, true, None, 2)
           | Greater -> (Some t, 0, false, None, 2))
      | Two (left, elt', right)
      | OneTwo (left, elt', right)
      | TwoOne (left, elt', right)
        ->
        (match do_compare compare elt elt' with
         | Less ->
           let (left_left, left_left_height_decrease, found_opt, left_right, left_right_height_decrease) =
             split left elt ~compare
           in
           let (right, height_increased) =
             match left_right with
             (* CR wduff: Eww. *)
             | None -> (right, Height_increase.Height_unchanged)
             | Some left_right ->
               let height_difference =
                 match t with
                 | Two _ -> left_right_height_decrease
                 | OneTwo _ -> left_right_height_decrease + 1
                 | TwoOne _ -> left_right_height_decrease - 1
                 | _ -> assert false
               in
               match height_difference with
               | -1 ->
                 (* This means we're in the TwoOne case, and height left_right = height left, which
                    means we can just reconstruct the node. *)
                 (TwoOne (left_right, elt', right), Height_unchanged)
               | _ ->
                 join_into_right
                   left_right
                   elt'
                   right
                   ~height_difference
           in
           (left_left,
            left_left_height_decrease + 1,
            found_opt,
            Some right,
            1 - Height_increase.to_int height_increased)
         | Equal -> (Some left, 1, true, Some right, 1)
         | Greater ->
           let (right_left, right_left_height_decrease, found_opt, right_right, right_right_height_decrease) =
             split left elt ~compare
           in
           let (left, height_increased) =
             match right_left with
             (* CR wduff: Eww. *)
             | None -> (left, Height_increase.Height_unchanged)
             | Some right_left ->
               let height_difference =
                 match t with
                 | Two _ -> right_left_height_decrease
                 | OneTwo _ -> right_left_height_decrease - 1
                 | TwoOne _ -> right_left_height_decrease + 1
                 | _ -> assert false
               in
               match height_difference with
               | -1 ->
                 (* This means we're in the OneTwo case, and height right_left = height right, which
                    means we can just reconstruct the node. *)
                 (OneTwo (left, elt', right_left), Height_unchanged)
               | _ ->
                 join_into_left
                   left
                   elt'
                   right_left
                   ~height_difference
           in
           (Some left,
            1 - Height_increase.to_int height_increased,
            found_opt,
            right_right,
            right_right_height_decrease + 1))
    ;;

    let rec union' set1 height1 set2 height2 ~compare =
      let (small, small_height, large, large_height) =
        if height1 <= height2
        then set1, height1, set2, height2
        else set2, height2, set1, height1
      in
      match small with
      | Leaf1 elt ->
        let (t, height_increased) = add' large elt ~compare in
        (t, large_height + Height_increase.to_int height_increased)
      | Leaf2 (elt1, elt2) ->
        let (t, height_increased1) = add' large elt1 ~compare in
        let (t, height_increased2) = add' t elt2 ~compare in
        (t, large_height + Height_increase.to_int height_increased1 + Height_increase.to_int height_increased2)
      | Two (small_left, elt, small_right)
      | OneTwo (small_left, elt, small_right)
      | TwoOne (small_left, elt, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, _, large_right, right_height_decrease) =
          split large elt ~compare
        in
        let left, left_height =
          match large_left with
          | None -> (small_left, small_left_height)
          | Some large_left ->
            union'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~compare
        in
        let right, right_height =
          match large_right with
          | None -> (small_right, small_right_height)
          | Some large_right ->
            union'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~compare
        in
        join left left_height elt right right_height
    ;;

    let union set1 set2 ~compare =
      union' set1 (height set1) set2 (height set2) ~compare
      |> fst
    ;;

    let rec inter' set1 height1 set2 height2 ~compare =
      let (small, small_height, large, large_height) =
        if height1 <= height2
        then (set1, height1, set2, height2)
        else (set2, height2, set1, height1)
      in
      match small with
      | Leaf1 elt ->
        (match mem large elt ~compare with
         | false -> None
         | true -> Some (Leaf1 elt, 1))
      | Leaf2 (elt1, elt2) ->
        (match (mem large elt1 ~compare, mem large elt2 ~compare) with
         | false, false -> None
         | true, false -> Some (Leaf1 elt1, 1)
         | false, true -> Some (Leaf1 elt2, 1)
         | true, true -> Some (Leaf2 (elt1, elt2), 2))
      | Two (small_left, elt, small_right)
      | OneTwo (small_left, elt, small_right)
      | TwoOne (small_left, elt, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_was_found, large_right, right_height_decrease) =
          split large elt ~compare
        in
        let left_opt =
          match large_left with
          | None -> None
          | Some large_left ->
            inter'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~compare
        in
        let right_opt =
          match large_right with
          | None -> None
          | Some large_right ->
            inter'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~compare
        in
        match left_opt, right_opt with
        | None, None -> None
        | Some (t, height), None | None, Some (t, height) ->
          (match large_was_found with
           | false -> Some (t, height)
           | true ->
             let (t, height_increased) = add' t elt ~compare in
             Some (t, height + Height_increase.to_int height_increased))
        | Some (left, left_height), Some (right, right_height) ->
          (match large_was_found with
           | false -> Some (join0 left left_height right right_height)
           | true ->
             Some (join left left_height elt right right_height))
    ;;

    let inter set1 set2 ~compare =
      inter' set1 (height set1) set2 (height set2) ~compare
      |> Option.map ~f:fst
    ;;

    (* CR wduff: Check that these calls to Option.set and Option.bind don't incur a closure
       allocation. *)
    let rec xor' set1 height1 set2 height2 ~compare =
      let (small, small_height, large, large_height) =
        if height1 <= height2
        then set1, height1, set2, height2
        else set2, height2, set1, height1
      in
      match small with
      | Leaf1 elt ->
        (* CR wduff: We could consider making some one-pass way of doing this. It would roughly
           be generic_add, but where on_elt_present can return none, thus switching to a remove. *)
        (match mem large elt ~compare with
         | true ->
           remove' large elt ~compare
           |> Option.map ~f:(fun (t, height_decreased) ->
             (t, large_height - Height_decrease.to_int height_decreased))
         | false ->
           let (t, height_increased) = add' large elt ~compare in
           Some (t, large_height + Height_increase.to_int height_increased))
      | Leaf2 (elt1, elt2) ->
        (let open Option.Let_syntax in
         match (mem large elt1 ~compare, mem large elt2 ~compare) with
         | true, true ->
           let%bind (t, height_decreased1) = remove' large elt1 ~compare in
           let%bind (t, height_decreased2) = remove' t elt2 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased1 - Height_decrease.to_int height_decreased2)
         | true, false ->
           let%bind (t, height_decreased) = remove' large elt1 ~compare in
           let (t, height_increased) = add' t elt2 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased)
         | false, true ->
           let%bind (t, height_decreased) = remove' large elt2 ~compare in
           let (t, height_increased) = add' t elt1 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased)
         | false, false ->
           let (t, height_increased1) = add' large elt1 ~compare in
           let (t, height_increased2) = add' t elt2 ~compare in
           return (t, large_height + Height_increase.to_int height_increased1 + Height_increase.to_int height_increased2))
      | Two (small_left, elt, small_right)
      | OneTwo (small_left, elt, small_right)
      | TwoOne (small_left, elt, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_was_found, large_right, right_height_decrease) =
          split large elt ~compare
        in
        let left_opt =
          match large_left with
          | None -> Some (small_left, small_left_height)
          | Some large_left ->
            xor'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~compare
        in
        let right_opt =
          match large_right with
          | None -> Some (small_right, small_right_height)
          | Some large_right ->
            xor'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~compare
        in
        match left_opt, right_opt with
        | None, None -> None
        | Some (t, height), None | None, Some (t, height) ->
          (match large_was_found with
           | false -> Some (t, height)
           | true ->
             remove' t elt ~compare
             |> Option.map ~f:(fun (t, height_decreased) ->
               (t, height - Height_decrease.to_int height_decreased)))
        | Some (left, left_height), Some (right, right_height) ->
          (match large_was_found with
           | false -> Some (join left left_height elt right right_height)
           | true -> Some (join0 left left_height right right_height))
    ;;

    let xor set1 set2 ~compare =
      xor' set1 (height set1) set2 (height set2) ~compare
      |> Option.map ~f:fst
    ;;

    let rec diff' set1 height1 set2 height2 ~flipped ~compare =
      let (small, small_height, large, large_height, flipped) =
        if height1 <= height2
        then (set1, height1, set2, height2, flipped)
        else (set2, height2, set1, height1, not flipped)
      in
      match small with
      | Leaf1 elt ->
        (if flipped
         then begin
           remove' large elt ~compare
           |> Option.map ~f:(fun (t, height_decreased) ->
             (t, large_height - Height_decrease.to_int height_decreased))
         end
         else begin
           match mem large elt ~compare with
           | true -> None
           | false -> Some (Leaf1 elt, 1)
         end)
      | Leaf2 (elt1, elt2) ->
        (if flipped
         then begin
           let open Option.Let_syntax in
           let%bind (t, height_decreased1) = remove' large elt1 ~compare in
           let%bind (t, height_decreased2) = remove' t elt2 ~compare in
           Some (t, large_height - Height_decrease.to_int height_decreased1 - Height_decrease.to_int height_decreased2)
         end
         else begin
           match (mem large elt1 ~compare, mem large elt2 ~compare) with
           | true, true -> None
           | false, true -> Some (Leaf1 elt1, 1)
           | true, false -> Some (Leaf1 elt2, 1)
           | false, false -> Some (Leaf2 (elt1, elt2), 2)
         end)
      | Two (small_left, elt, small_right)
      | OneTwo (small_left, elt, small_right)
      | TwoOne (small_left, elt, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_was_found, large_right, right_height_decrease) =
          split large elt ~compare
        in
        let left_opt =
          match large_left with
          | None -> None
          | Some large_left ->
            diff'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~flipped
              ~compare
        in
        let right_opt =
          match large_right with
          | None -> None
          | Some large_right ->
            diff'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~flipped
              ~compare
        in
        match left_opt, right_opt with
        | None, None -> None
        | Some (t, height), None | None, Some (t, height) ->
          (if flipped
           then Some (t, height)
           else begin
             match large_was_found with
             | true -> Some (t, height)
             | false ->
               let (t, height_increased) = add' t elt ~compare in
               Some (t, height + Height_increase.to_int height_increased)
           end)
        | Some (left, left_height), Some (right, right_height) ->
          (if flipped
           then Some (join0 left left_height right right_height)
           else begin
             match large_was_found with
             | true -> Some (join0 left left_height right right_height)
             | false ->
               Some (join left left_height elt right right_height)
           end)
    ;;

    let diff set1 set2 ~compare =
      diff' set1 (height set1) set2 (height set2) ~flipped:false ~compare
      |> Option.map ~f:fst
    ;;
  end

  type ('a, 'cmp) t = 'a Balanced_tree.t [@@deriving sexp_of]

  let height = Balanced_tree.height
  let length = Balanced_tree.length

  let empty = Balanced_tree.empty
  let is_empty = Balanced_tree.is_empty
  let of_non_empty = Balanced_tree.of_non_empty
  let of_non_empty_option = Balanced_tree.of_non_empty_option
  let get_non_empty = Balanced_tree.get_non_empty
  let get_non_empty_exn = Balanced_tree.get_non_empty_exn

  let singleton = Balanced_tree.singleton

  let of_sorted_balanced_tree_unchecked balanced_tree = balanced_tree

  let of_sorted_balanced_tree_exn balanced_tree ~compare =
    match balanced_tree with
    | None -> None
    | Some non_empty_balanced_tree ->
      Some (Non_empty.of_sorted_balanced_tree_exn non_empty_balanced_tree ~compare)
  ;;

  let to_balanced_tree t = t

  let of_sorted_array_unchecked array =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_sorted_array_unchecked array)
  ;;

  let of_sorted_array_exn array ~compare =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_sorted_array_exn array ~compare)
  ;;

  let of_array array ~compare =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_array array ~compare)
  ;;

  let of_sorted_list_unchecked list =
    if List.is_empty list
    then None
    else Some (Non_empty.of_sorted_list_unchecked list)
  ;;

  let of_sorted_list_exn list ~compare =
    if List.is_empty list
    then None
    else Some (Non_empty.of_sorted_list_exn list ~compare)
  ;;

  let of_list list ~compare =
    if List.is_empty list
    then None
    else Some (Non_empty.of_list list ~compare)
  ;;

  let to_list = Balanced_tree.to_list
  let iter = Balanced_tree.iter
  let fold = Balanced_tree.fold
  let fold_right = Balanced_tree.fold_right

  let resorting_map t ~f ~compare =
    match t with
    | None -> None
    | Some non_empty -> Some (Non_empty.resorting_map non_empty ~f ~compare)
  ;;

  let mem t elt ~compare =
    match t with
    | None -> false
    | Some non_empty -> Non_empty.mem non_empty elt ~compare
  ;;

  let add_non_empty t elt ~compare =
    match t with
    | None -> Non_empty.singleton elt
    | Some non_empty -> Non_empty.add non_empty elt ~compare
  ;;

  let add t elt ~compare =
    Some (add_non_empty t elt ~compare)
  ;;

  let strict_add_non_empty t elt ~compare =
    match t with
    | None -> `Ok (Non_empty.singleton elt)
    | Some non_empty -> Non_empty.strict_add non_empty elt ~compare
  ;;

  let strict_add t elt ~compare =
    match strict_add_non_empty t elt ~compare with
    | `Duplicate_elt -> `Duplicate_elt
    | `Ok non_empty -> `Ok (Some non_empty)
  ;;

  let strict_add_non_empty_exn t elt ~compare =
    match t with
    | None -> Non_empty.singleton elt
    | Some non_empty -> Non_empty.strict_add_exn non_empty elt ~compare
  ;;

  let strict_add_exn t elt ~compare =
    Some (strict_add_non_empty_exn t elt ~compare)
  ;;

  let generic_add_non_empty t elt ~on_already_present ~compare =
    match t with
    | None -> Non_empty.singleton elt
    | Some non_empty -> Non_empty.generic_add non_empty elt ~on_already_present ~compare
  ;;

  let generic_add t elt ~on_already_present ~compare =
    Some (generic_add_non_empty t elt ~on_already_present ~compare)
  ;;

  let remove t elt ~compare =
    match t with
    | None -> None
    | Some non_empty -> Non_empty.remove non_empty elt ~compare
  ;;

  let strict_remove t elt ~compare =
    match t with
    | None -> `Not_found
    | Some non_empty -> Non_empty.strict_remove non_empty elt ~compare
  ;;

  let strict_remove_exn t elt ~compare =
    match t with
    | None ->
      (* CR wduff: Share this error with the [Non_empty] code. *)
      raise_s [%message]
    | Some non_empty -> Non_empty.strict_remove_exn non_empty elt ~compare
  ;;

  let union set1 set2 ~compare =
    match (set1, set2) with
    | (None, None) -> None
    | (Some non_empty, None) | (None, Some non_empty) -> Some non_empty
    | (Some non_empty1, Some non_empty2) ->
      Some (Non_empty.union non_empty1 non_empty2 ~compare)
  ;;

  let inter set1 set2 ~compare =
    match (set1, set2) with
    | (None, _) | (_, None) -> None
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.inter non_empty1 non_empty2 ~compare
  ;;

  let xor set1 set2 ~compare =
    match (set1, set2) with
    | (None, None) -> None
    | (None, set) | (set, None) -> set
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.xor non_empty1 non_empty2 ~compare
  ;;

  let diff set1 set2 ~compare =
    match (set1, set2) with
    | (_, None) -> set1
    | (None, _) -> None
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.diff non_empty1 non_empty2 ~compare
  ;;

  let find_min t =
    Option.map t ~f:Non_empty.find_min
  ;;

  let find_max t =
    Option.map t ~f:Non_empty.find_max
  ;;

  let find_min_exn t =
    get_non_empty_exn t
    |> Non_empty.find_min
  ;;

  let find_max_exn t =
    get_non_empty_exn t
    |> Non_empty.find_max
  ;;

  let remove_min t =
    Option.bind t ~f:Non_empty.remove_min
  ;;

  let remove_max t =
    Option.bind t ~f:Non_empty.remove_max
  ;;

  let find_and_remove_min t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (min, t) = Non_empty.find_and_remove_min non_empty in
      (Some min, t)
  ;;

  let find_and_remove_max t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (max, t) = Non_empty.find_and_remove_max non_empty in
      (Some max, t)
  ;;

  module type Specialized =
    Specialized_set
    with type 'a balanced_tree := 'a Balanced_tree.t
    with type 'a non_empty_balanced_tree := 'a Balanced_tree.Non_empty.t
    with type ('a, 'cmp) generic_set := ('a, 'cmp) t
    with type ('a, 'cmp) non_empty_generic_set := ('a, 'cmp) Non_empty.t

  module Make_using_comparator (Elt : Comparator) : Specialized
    with type elt = Elt.t
    with type compare_witness = Elt.compare_witness
  =
  struct
    type elt = Elt.t [@@deriving sexp_of]
    type compare_witness = Elt.compare_witness
    let sexp_of_compare_witness = [%sexp_of: _]

    let compare = Elt.compare

    type nonrec t = (elt, compare_witness) t [@@deriving sexp_of]

    module Non_empty = struct
      type nonrec elt = elt [@@deriving sexp_of]
      type nonrec compare_witness = compare_witness [@@deriving sexp_of]

      let compare = Elt.compare

      type t = (elt, compare_witness) Non_empty.t [@@deriving sexp_of]

      let height = Non_empty.height
      let length = Non_empty.length
      let singleton = Non_empty.singleton
      let to_list = Non_empty.to_list
      let iter = Non_empty.iter
      let fold = Non_empty.fold
      let fold_right = Non_empty.fold_right
      let of_array = Non_empty.of_array ~compare
      let of_sorted_array_unchecked = Non_empty.of_sorted_array_unchecked
      let of_sorted_array_exn = Non_empty.of_sorted_array_exn ~compare
      let of_list = Non_empty.of_list ~compare
      let of_sorted_list_unchecked = Non_empty.of_sorted_list_unchecked
      let of_sorted_list_exn = Non_empty.of_sorted_list_exn ~compare
      let of_sorted_balanced_tree_unchecked = Non_empty.of_sorted_balanced_tree_unchecked
      let of_sorted_balanced_tree_exn = Non_empty.of_sorted_balanced_tree_exn ~compare
      let to_balanced_tree = Non_empty.to_balanced_tree
      let resorting_map' = Non_empty.resorting_map
      let resorting_map = Non_empty.resorting_map ~compare
      let mem = Non_empty.mem ~compare
      let add = Non_empty.add ~compare
      let strict_add = Non_empty.strict_add ~compare
      let strict_add_exn = Non_empty.strict_add_exn ~compare
      let generic_add = Non_empty.generic_add ~compare
      let union = Non_empty.union ~compare
      let remove = Non_empty.remove ~compare
      let strict_remove = Non_empty.strict_remove ~compare
      let strict_remove_exn = Non_empty.strict_remove_exn ~compare
      let inter = Non_empty.inter ~compare
      let xor = Non_empty.xor ~compare
      let diff = Non_empty.diff ~compare
      let find_min = Non_empty.find_min
      let remove_min = Non_empty.remove_min
      let find_and_remove_min = Non_empty.find_and_remove_min
      let find_max = Non_empty.find_max
      let remove_max = Non_empty.remove_max
      let find_and_remove_max = Non_empty.find_and_remove_max
    end

    let height = height
    let length = length
    let singleton = singleton
    let to_list = to_list
    let iter = iter
    let fold = fold
    let fold_right = fold_right
    let of_array = of_array ~compare
    let of_sorted_array_unchecked = of_sorted_array_unchecked
    let of_sorted_array_exn = of_sorted_array_exn ~compare
    let of_list = of_list ~compare
    let of_sorted_list_unchecked = of_sorted_list_unchecked
    let of_sorted_list_exn = of_sorted_list_exn ~compare
    let of_sorted_balanced_tree_unchecked = of_sorted_balanced_tree_unchecked
    let of_sorted_balanced_tree_exn = of_sorted_balanced_tree_exn ~compare
    let to_balanced_tree = to_balanced_tree
    let resorting_map' = resorting_map
    let resorting_map = resorting_map ~compare
    let mem = mem ~compare
    let add = add ~compare
    let strict_add = strict_add ~compare
    let strict_add_exn = strict_add_exn ~compare
    let generic_add = generic_add ~compare
    let union = union ~compare
    let empty = empty
    let is_empty = is_empty
    let of_non_empty = of_non_empty
    let of_non_empty_option = of_non_empty_option
    let get_non_empty = get_non_empty
    let get_non_empty_exn = get_non_empty_exn
    let add_non_empty = add_non_empty ~compare
    let strict_add_non_empty = strict_add_non_empty ~compare
    let strict_add_non_empty_exn = strict_add_non_empty_exn ~compare
    let generic_add_non_empty = generic_add_non_empty ~compare
    let remove = remove ~compare
    let strict_remove = strict_remove ~compare
    let strict_remove_exn = strict_remove_exn ~compare
    let inter = inter ~compare
    let xor = xor ~compare
    let diff = diff ~compare
    let find_min = find_min
    let find_min_exn = find_min_exn
    let remove_min = remove_min
    let find_and_remove_min = find_and_remove_min
    let find_max = find_max
    let find_max_exn = find_max_exn
    let remove_max = remove_max
    let find_and_remove_max = find_and_remove_max
  end

  module Make (Elt : Comparable) = Make_using_comparator (struct include Elt include Compare.Make (Elt) end)
end

module Map = struct
  module Balanced_tree = Balanced_tree2

  module Non_empty
    : Non_empty_map
      with type ('a, 'cmp) set := 'a Tree.Non_empty.t
      with type ('a, 'b) balanced_tree := ('a, 'b) Balanced_tree.Non_empty.t
      with type ('k, 'v, 'cmp) maybe_empty := ('k, 'v) Balanced_tree.t
      with type ('k, 'v, 'cmp) t = ('k, 'v) Balanced_tree.Non_empty.t =
  struct
    module Balanced_tree = Balanced_tree.Non_empty
    (* CR wduff: Eww. *)
    open Tree2.Non_empty

    type ('k, 'v, 'cmp) t = ('k, 'v) Balanced_tree.t [@@deriving sexp_of]

    let rec check_sorted'' t ~left_max ~compare =
      match t with
      | Leaf1 (key, _) ->
        check_less left_max key ~compare;
        key
      | Leaf2 (key1, _, key2, _) ->
        check_less left_max key1 ~compare;
        check_less key1 key2 ~compare;
        key2
      | Two (left, key, _, right) | OneTwo (left, key, _, right) | TwoOne (left, key, _, right) ->
        let left_max = check_sorted'' left ~left_max ~compare in
        check_less left_max key ~compare;
        check_sorted'' right ~left_max:key ~compare

    let rec check_sorted' t ~compare =
      match t with
      | Leaf1 (key, _) -> key
      | Leaf2 (key1, _, key2, _) ->
        check_less key1 key2 ~compare;
        key2
      | Two (left, key, _, right) | OneTwo (left, key, _, right) | TwoOne (left, key, _, right) ->
        let left_max = check_sorted' left ~compare in
        check_less left_max key ~compare;
        check_sorted'' right ~left_max:key ~compare
    ;;

    (* CR wduff: Consider checking this in debug mode. *)
    let check_sorted (t : ('k, 'v, 'cmp) t) ~compare =
      ignore (check_sorted' t ~compare : 'k)
    ;;

    let height = Balanced_tree.height
    let length = Balanced_tree.length
    let singleton ~key ~data = Balanced_tree.singleton key data
    let of_sorted_array_unchecked = Balanced_tree.of_array
    let of_sorted_list_unchecked = Balanced_tree.of_list
    let to_list = Balanced_tree.to_pair_list
    let keys = Balanced_tree.to_list1
    let key_set = Balanced_tree.to_tree1
    let data = Balanced_tree.to_list2
    let map t ~f = Balanced_tree.map2 t ~f
    let iter = Balanced_tree.iter2
    let iteri t ~f = Balanced_tree.iter_both t ~f:(fun key data -> f ~key ~data)
    let fold = Balanced_tree.fold2
    let foldi t ~init ~f = Balanced_tree.fold_both t ~init ~f:(fun acc key data -> f acc ~key ~data)
    let fold_right = Balanced_tree.fold2_right
    let fold_righti t ~init ~f = Balanced_tree.fold_both_right t ~init ~f:(fun key data acc -> f ~key ~data acc)
    let fold_map = Balanced_tree.fold_map2
    let fold_mapi t ~init ~f =
      Balanced_tree.fold_map_both t ~init ~f:(fun acc key data ->
        let (acc, data) = f acc ~key ~data in
        acc, key, data)
    ;;

    let rekeying_map (type key) t ~f ~compare =
      let compare_key = convert_compare compare in
      let array =
        List.to_array (to_list t)
        |> Array.map ~f:(fun (key, data) -> f ~key ~data)
      in
      Array.sort array ~compare:[%compare: key * _];
      of_sorted_array_unchecked array
    ;;

    let two_left_maybe_grew = Balanced_tree.two_left_maybe_grew
    let one_two_left_maybe_grew = Balanced_tree.one_two_left_maybe_grew
    let two_one_left_maybe_grew = Balanced_tree.two_one_left_maybe_grew
    let two_right_maybe_grew = Balanced_tree.two_right_maybe_grew
    let one_two_right_maybe_grew = Balanced_tree.one_two_right_maybe_grew
    let two_one_right_maybe_grew = Balanced_tree.two_one_right_maybe_grew
    let two_left_maybe_shrank = Balanced_tree.two_left_maybe_shrank
    let one_two_left_maybe_shrank = Balanced_tree.one_two_left_maybe_shrank
    let two_one_left_maybe_shrank = Balanced_tree.two_one_left_maybe_shrank
    let two_right_maybe_shrank = Balanced_tree.two_right_maybe_shrank
    let one_two_right_maybe_shrank = Balanced_tree.one_two_right_maybe_shrank
    let two_one_right_maybe_shrank = Balanced_tree.two_one_right_maybe_shrank
    let find_min = Balanced_tree.find_leftmost
    let find_max = Balanced_tree.find_rightmost
    let remove_min = Balanced_tree.remove_leftmost
    let remove_max = Balanced_tree.remove_rightmost
    let find_and_remove_min' = Balanced_tree.find_and_remove_leftmost'
    let find_and_remove_min = Balanced_tree.find_and_remove_leftmost
    let find_and_remove_max' = Balanced_tree.find_and_remove_rightmost'
    let find_and_remove_max = Balanced_tree.find_and_remove_rightmost
    let join_into_left = Balanced_tree.join_into_left
    let join_into_right = Balanced_tree.join_into_right
    let join = Balanced_tree.join
    let join0 = Balanced_tree.join0

    let of_sorted_balanced_tree_unchecked balanced_tree = balanced_tree

    let of_sorted_balanced_tree_exn balanced_tree ~compare =
      check_sorted balanced_tree ~compare;
      of_sorted_balanced_tree_unchecked balanced_tree
    ;;

    let to_balanced_tree t = t

    let of_sorted_array_exn (type key) array ~compare =
      let compare_key = convert_compare compare in
      if Array.is_sorted array ~compare:[%compare: key * _]
      then of_sorted_array_unchecked array
      else
        (* CR wduff: *)
        raise_s [%message]
    ;;

    let of_array (type key) array ~compare =
      let compare_key = convert_compare compare in
      let copy = Array.copy array in
      Array.sort copy ~compare:[%compare: key * _];
      of_sorted_array_unchecked copy
    ;;

    let of_sorted_list_exn (type key) list ~compare =
      let compare_key = convert_compare compare in
      if List.is_sorted list ~compare:[%compare: key * _]
      then of_sorted_list_unchecked list
      else
        (* CR wduff: *)
        raise_s [%message]
    ;;

    let of_list (type key) list ~compare =
      let compare_key = convert_compare compare in
      let array = Array.of_list list in
      Array.sort array ~compare:[%compare: key * _];
      of_sorted_array_unchecked array
    ;;

    (* CR wduff: Expose this? *)
    let rec find_and_call t key ~if_found ~if_not_found ~compare =
      match t with
      | Leaf1 (key', data) ->
        (match do_compare compare key key' with
         | Equal -> if_found data
         | Less | Greater -> if_not_found ())
      | Leaf2 (key1, data1, key2, data2) ->
        (match do_compare compare key key1 with
         | Equal -> if_found data1
         | Less | Greater ->
           (match do_compare compare key key2 with
            | Equal -> if_found data2
            | Less | Greater -> if_not_found ()))
      | Two (left, key', data, right)
      | OneTwo (left, key', data, right)
      | TwoOne (left, key', data, right)
        ->
        match do_compare compare key key' with
        | Less -> find_and_call left key ~if_found ~if_not_found  ~compare
        | Equal -> if_found data
        | Greater -> find_and_call right key ~if_found ~if_not_found ~compare
    ;;

    let find t key ~compare =
      find_and_call t key ~if_found:Option.some ~if_not_found:(fun () -> None) ~compare
    ;;

    let find_exn t key ~compare =
      (* CR wduff: Improve error message? *)
      find_and_call t key ~if_found:Fn.id ~if_not_found:(fun () -> raise (Not_found_s [%message])) ~compare
    ;;

    let mem t key ~compare =
      find_and_call t key ~if_found:(fun _ -> true) ~if_not_found:(fun () -> false) ~compare
    ;;

    let rec generic_add' t ~key ~data ~on_already_present ~compare =
      match t with
      | Leaf1 (key', data') ->
        (match do_compare compare key key' with
         | Less -> (Leaf2 (key, data, key', data'), Height_increased)
         | Equal -> (Leaf1 (key, on_already_present ~key ~old_data:data' ~new_data:data), Height_unchanged)
         | Greater -> (Leaf2 (key', data', key, data), Height_increased))
      | Leaf2 (key1, data1, key2, data2) ->
        let t =
          (match do_compare compare key key1 with
           | Less -> Two (Leaf1 (key, data), key1, data1, Leaf1 (key2, data2))
           | Equal ->
             Leaf2 (key, on_already_present ~key ~old_data:data1 ~new_data:data, key2, data2)
           | Greater ->
             match do_compare compare key key2 with
             | Less -> Two (Leaf1 (key1, data1), key, data, Leaf1 (key2, data2))
             | Equal ->
               Leaf2 (key1, data1, key, on_already_present ~key ~old_data:data2 ~new_data:data)
             | Greater -> Two (Leaf1 (key1, data1), key2, data2, Leaf1 (key, data)))
        in
        (t, Height_unchanged)
      | Two (left, key', data', right) ->
        (match do_compare compare key key' with
         | Less ->
           let (left, height_increased) =
             generic_add' left ~key ~data ~on_already_present ~compare
           in
           two_left_maybe_grew (left, height_increased) key' data' right
         | Equal ->
           let data = on_already_present ~key ~old_data:data' ~new_data:data in
           (Two (left, key, data, right), Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right ~key ~data ~on_already_present ~compare
           in
           two_right_maybe_grew left key' data' (right, height_increased))
      | OneTwo (left, key', data', right) ->
        (match do_compare compare key key' with
         | Less ->
           let (left, height_increased) =
             generic_add' left ~key ~data ~on_already_present ~compare
           in
           one_two_left_maybe_grew (left, height_increased) key' data' right
         | Equal ->
           let data = on_already_present ~key ~old_data:data' ~new_data:data in
           (OneTwo (left, key, data, right), Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right ~key ~data ~on_already_present ~compare
           in
           one_two_right_maybe_grew left key' data' (right, height_increased))
      | TwoOne (left, key', data', right) ->
        (match do_compare compare key key' with
         | Less ->
           let (left, height_increased) =
             generic_add' left ~key ~data ~on_already_present ~compare
           in
           two_one_left_maybe_grew (left, height_increased) key' data' right
         | Equal ->
           let data = on_already_present ~key ~old_data:data' ~new_data:data in
           (TwoOne (left, key, data, right), Height_unchanged)
         | Greater ->
           let (right, height_increased) =
             generic_add' right ~key ~data ~on_already_present ~compare
           in
           two_one_right_maybe_grew left key' data' (right, height_increased))
    ;;

    let generic_add t ~key ~data ~on_already_present ~compare =
      let (t, _height_increased) = generic_add' t ~key ~data ~on_already_present ~compare in
      t
    ;;

    let set' t ~key ~data ~compare =
      let on_already_present ~key:_ ~old_data:_ ~new_data = new_data in
      generic_add' t ~key ~data ~compare ~on_already_present
    ;;

    (* CR wduff: Should this use set' instead? *)
    let set t ~key ~data ~compare =
      let on_already_present ~key:_ ~old_data:_ ~new_data = new_data in
      generic_add t ~key ~data ~compare ~on_already_present
    ;;

    let add_exn t ~key ~data ~compare =
      (* CR wduff: Better error and/or faster error. *)
      let on_already_present ~key:_ ~old_data:_ ~new_data:_ = raise_s [%message] in
      generic_add t ~key ~data ~compare ~on_already_present
    ;;

    let add t ~key ~data ~compare =
      match add_exn t ~key ~data ~compare with
      | t -> `Ok t
      | exception _ -> `Duplicate_key
    ;;

    (* CR wduff: Special case unchanged so that we don't have to rebuild the spine? *)
    let rec remove' t key ~compare =
      match t with
      | Leaf1 (key', _) ->
        (match do_compare compare key key' with
         | Equal -> None
         | Less | Greater -> Some (t, Height_unchanged))
      | Leaf2 (key1, data1, key2, data2) ->
        (match do_compare compare key key1 with
         | Equal -> Some (Leaf1 (key2, data2), Height_decreased)
         | Less | Greater ->
           match do_compare compare key key2 with
           | Equal -> Some (Leaf1 (key1, data1), Height_decreased)
           | Less | Greater -> Some (t, Height_unchanged))
      | Two (left, key', data', right) ->
        let t_with_height_decreased =
          match do_compare compare key key' with
         | Less ->
           two_left_maybe_shrank (remove' left key ~compare)  key' data' right
         | Equal ->
           let ((right_min_key, right_min_data), right_opt) =
             find_and_remove_min' right
           in
           two_right_maybe_shrank left  right_min_key right_min_data right_opt
         | Greater ->
           two_right_maybe_shrank left  key' data' (remove' right key ~compare)
        in
        Some t_with_height_decreased
      | OneTwo (left, key', data', right) ->
        let t_with_height_decreased =
          match do_compare compare key key' with
          | Less ->
            one_two_left_maybe_shrank (remove' left key ~compare)  key' data' right
          | Equal ->
            let ((right_min_key, right_min_data), right_opt) =
              find_and_remove_min' right
            in
            one_two_right_maybe_shrank left  right_min_key right_min_data right_opt
          | Greater ->
            one_two_right_maybe_shrank left  key' data' (remove' right key ~compare)
        in
        Some t_with_height_decreased
      | TwoOne (left, key', data', right) ->
        let t_with_height_decreased =
          match do_compare compare key key' with
          | Less ->
            two_one_left_maybe_shrank (remove' left key ~compare)  key' data' right
          | Equal ->
            let ((left_max_key, left_max_data), left_opt) =
              find_and_remove_max' left
            in
            two_one_left_maybe_shrank left_opt left_max_key left_max_data right
          | Greater ->
            two_one_right_maybe_shrank left  key' data' (remove' right key ~compare)
        in
        Some t_with_height_decreased
    ;;

    let remove t key ~compare =
      match remove' t key ~compare with
      | None -> None
      | Some (t, _height_decreased) -> Some t
    ;;

    (* CR wduff: Optimize this. *)
    let find_and_remove t key ~compare =
      let find_result = find t key ~compare in
      match find_result with
      | None -> None
      | Some data -> Some (data, remove t key ~compare)
    ;;

    let rec split t key ~compare =
      match t with
      | Leaf1 (key', data) ->
        (match do_compare compare key key' with
         | Less -> (None, 1, None, Some t, 0)
         | Equal -> (None, 1, Some data, None, 1)
         | Greater -> (Some t, 0, None, None, 1))
      | Leaf2 (key1, data1, key2, data2) ->
        (match do_compare compare key key1 with
         | Less -> (None, 2, None, Some t, 0)
         | Equal -> (None, 2, Some data1, Some (Leaf1 (key2, data2)), 1)
         | Greater ->
           (match do_compare compare key key2 with
            | Less -> (Some (Leaf1 (key1, data1)), 1, None, Some (Leaf1 (key2, data2)), 1)
            | Equal -> (Some (Leaf1 (key1, data1)), 1, Some data2, None, 2)
            | Greater -> (Some t, 0, None, None, 2)))
      | Two (left, key', data, right)
      | OneTwo (left, key', data, right)
      | TwoOne (left, key', data, right)
        ->
        let (extra_left_decrease, extra_right_decrease) =
          match t with
          | Two _ -> (0, 0)
          | OneTwo _ -> (1, 0)
          | TwoOne _ -> (0, 1)
          | _ -> assert false
        in
        (match do_compare compare key key' with
         | Less ->
           let (left_left, left_left_height_decrease, found_opt, left_right, left_right_height_decrease) =
             split left key ~compare
           in
           let (right, right_height_increase) =
             match left_right with
             | None ->
               (* CR wduff: We can probably do this faster if we have [add_min]. *)
               let (right, height_increased) = set' right ~key:key' ~data ~compare in
               (right, Height_increase.to_int height_increased)
             | Some left_right ->
               let height_difference =
                 left_right_height_decrease + extra_left_decrease - extra_right_decrease
               in
               match height_difference with
               | -1 ->
                 (* This means we're in the TwoOne case, and height left_right = height left,
                    which means we can just reconstruct the node, which is a height increase of 2
                    relative to just the right. *)
                 (TwoOne (left_right, key', data, right), 2)
               | _ ->
                 let (right, height_increased) =
                   join_into_right
                     left_right
                     key'
                     data
                     right
                     ~height_difference
                 in
                 (right, Height_increase.to_int height_increased)
           in
           (left_left,
            1 + extra_left_decrease + left_left_height_decrease,
            found_opt,
            Some right,
            1 + extra_right_decrease - right_height_increase)
         | Equal -> (Some left, 1, Some data, Some right, 1)
         | Greater ->
           let (right_left, right_left_height_decrease, found_opt, right_right, right_right_height_decrease) =
             split right key ~compare
           in
           let (left, left_height_increase) =
             match right_left with
             | None ->
               (* CR wduff: We can probably do this faster if we have [add_max]. *)
               let (left, height_increased) = set' left ~key:key' ~data ~compare in
               (left, Height_increase.to_int height_increased)
             | Some right_left ->
               let height_difference =
                 right_left_height_decrease - extra_left_decrease + extra_right_decrease
               in
               match height_difference with
               | -1 ->
                 (* This means we're in the OneTwo case, and height right_left = height right,
                    which means we can just reconstruct the node, which is a height increase of 2
                    relative to just the left. *)
                 (OneTwo (left, key', data, right_left), 2)
               | _ ->
                 let (left, height_increased) =
                   join_into_left
                     left
                     key'
                     data
                     right_left
                     ~height_difference
                 in
                 (left, Height_increase.to_int height_increased)
           in
           (Some left,
            1 + extra_left_decrease - left_height_increase,
            found_opt,
            right_right,
            1 + extra_right_decrease + right_right_height_decrease))
    ;;

    let rec union' map1 height1 map2 height2 ~merge ~flip_merge ~compare =
      let (small, small_height, large, large_height, merge, flip_merge) =
        if height1 <= height2
        then map1, height1, map2, height2, merge, flip_merge
        else map2, height2, map1, height1, flip_merge, merge
      in
      (* CR wduff: Check that simply removing the labels doesn't result in a closure allocation. *)
      let on_already_present ~key ~old_data ~new_data = flip_merge ~key old_data new_data in
      match small with
      | Leaf1 (key, data) ->
        let (t, height_increased) = generic_add' large ~key ~data ~on_already_present ~compare in
        (t, large_height + Height_increase.to_int height_increased)
      | Leaf2 (key1, data1, key2, data2) ->
        let (t, height_increased1) =
          generic_add' large ~key:key1 ~data:data1 ~on_already_present ~compare
        in
        let (t, height_increased2) =
          generic_add' t ~key:key2 ~data:data2 ~on_already_present ~compare
        in
        (t, large_height + Height_increase.to_int height_increased1 + Height_increase.to_int height_increased2)
      | Two (small_left, key, small_data, small_right)
      | OneTwo (small_left, key, small_data, small_right)
      | TwoOne (small_left, key, small_data, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_data_opt, large_right, right_height_decrease) =
          split large key ~compare
        in
        let left, left_height =
          match large_left with
          | None -> (small_left, small_left_height)
          | Some large_left ->
            union'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~merge
              ~flip_merge
              ~compare
        in
        let right, right_height =
          match large_right with
          | None -> (small_right, small_right_height)
          | Some large_right ->
            union'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~merge
              ~flip_merge
              ~compare
        in
        let data =
          match large_data_opt with
          | None -> small_data
          | Some large_data -> merge ~key small_data large_data
        in
        join left left_height key data right right_height
    ;;

    let union map1 map2 ~merge ~compare =
      let flip_merge ~key data2 data1 = merge ~key data1 data2 in
      union' map1 (height map1) map2 (height map2) ~merge ~flip_merge ~compare
      |> fst
    ;;

    type ('k, 'v3, 'cmp) inter_swap =
      | T : ('k, 'v1, 'cmp) t
            * int
            * ('k, 'v2, 'cmp) t
            * int
            * (key:'k -> 'v1 -> 'v2 -> 'v3)
            * (key:'k -> 'v2 -> 'v1 -> 'v3)
            -> ('k, 'v3, 'cmp) inter_swap

    let rec inter'
      : type k v1 v2 v3 cmp.
        (k, v1, cmp) t
        -> int
        -> (k, v2, cmp) t
        -> int
        -> merge:(key:k -> v1 -> v2 -> v3)
        -> flip_merge:(key:k -> v2 -> v1 -> v3)
        -> compare:(k, cmp) compare
        -> ((k, v3, cmp) t * int) option
      =
      fun map1 height1 map2 height2 ~merge ~flip_merge ~compare ->
      let (T (small, small_height, large, large_height, merge, flip_merge)) =
        if height1 <= height2
        then T (map1, height1, map2, height2, merge, flip_merge)
        else T (map2, height2, map1, height1, flip_merge, merge)
      in
      match small with
      | Leaf1 (key, data) ->
        (match find large key ~compare with
         | None -> None
         | Some data' ->
           Some (Leaf1 (key, merge ~key data data'), 1))
      | Leaf2 (key1, data1, key2, data2) ->
        (match (find large key1 ~compare, find large key2 ~compare) with
         | None, None -> None
         | Some data1', None -> Some (Leaf1 (key1, merge ~key:key1 data1 data1'), 1)
         | None, Some data2' -> Some (Leaf1 (key2, merge ~key:key2 data2 data2'), 1)
         | Some data1', Some data2' ->
           Some (Leaf2 (key1, merge ~key:key1 data1 data1', key2, merge ~key:key2 data2 data2'), 2))
      | Two (small_left, key, small_data, small_right)
      | OneTwo (small_left, key, small_data, small_right)
      | TwoOne (small_left, key, small_data, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_data_opt, large_right, right_height_decrease) =
          split large key ~compare
        in
        let left_opt =
          match large_left with
          | None -> None
          | Some large_left ->
            inter'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~merge
              ~flip_merge
              ~compare
        in
        let right_opt =
          match large_right with
          | None -> None
          | Some large_right ->
            inter'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~merge
              ~flip_merge
              ~compare
        in
        match left_opt, right_opt with
        | None, None -> None
        | Some (t, height), None | None, Some (t, height) ->
          (match large_data_opt with
           | None -> Some (t, height)
           | Some large_data ->
             let (t, height_increased) = set' t ~key ~data:(merge ~key small_data large_data) ~compare in
             Some (t, height + Height_increase.to_int height_increased))
        | Some (left, left_height), Some (right, right_height) ->
          (match large_data_opt with
           | None -> Some (join0 left left_height right right_height)
           | Some large_data ->
             Some (join left left_height key (merge ~key small_data large_data) right right_height))
    ;;

    let inter map1 map2 ~merge ~compare =
      let flip_merge ~key data2 data1 = merge ~key data1 data2 in
      inter' map1 (height map1) map2 (height map2) ~merge ~flip_merge ~compare
      |> Option.map ~f:fst
    ;;

    (* CR wduff: Check that these calls to Option.map and Option.bind don't incur a closure
       allocation. *)
    let rec xor' map1 height1 map2 height2 ~compare =
      let (small, small_height, large, large_height) =
        if height1 <= height2
        then map1, height1, map2, height2
        else map2, height2, map1, height1
      in
      match small with
      | Leaf1 (key, data) ->
        (* CR wduff: We could consider making some one-pass way of doing this. It would roughly
           be generic_add, but where on_key_present can return none, thus switching to a remove. *)
        (match mem large key ~compare with
         | true ->
           remove' large key ~compare
           |> Option.map ~f:(fun (t, height_decreased) ->
             (t, large_height - Height_decrease.to_int height_decreased))
         | false ->
           let (t, height_increased) = set' large ~key ~data ~compare in
           Some (t, large_height + Height_increase.to_int height_increased))
      | Leaf2 (key1, data1, key2, data2) ->
        (let open Option.Let_syntax in
         match (mem large key1 ~compare, mem large key2 ~compare) with
         | true, true ->
           let%bind (t, height_decreased1) = remove' large key1 ~compare in
           let%bind (t, height_decreased2) = remove' t key2 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased1 - Height_decrease.to_int height_decreased2)
         | true, false ->
           let%bind (t, height_decreased) = remove' large key1 ~compare in
           let (t, height_increased) = set' t ~key:key2 ~data:data2 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased)
         | false, true ->
           let%bind (t, height_decreased) = remove' large key2 ~compare in
           let (t, height_increased) = set' t ~key:key1 ~data:data1 ~compare in
           return (t, large_height - Height_decrease.to_int height_decreased + Height_increase.to_int height_increased)
         | false, false ->
           let (t, height_increased1) = set' large ~key:key1 ~data:data1 ~compare in
           let (t, height_increased2) = set' t ~key:key2 ~data:data2 ~compare in
           return (t, large_height + Height_increase.to_int height_increased1 + Height_increase.to_int height_increased2))
      | Two (small_left, key, new_data, small_right)
      | OneTwo (small_left, key, new_data, small_right)
      | TwoOne (small_left, key, new_data, small_right)
        ->
        let (small_left_height, small_right_height) =
          match small with
          | Two _ -> (small_height - 1, small_height - 1)
          | OneTwo _ -> (small_height - 2, small_height - 1)
          | TwoOne _ -> (small_height - 1, small_height - 2)
          | _ -> assert false
        in
        let (large_left, left_height_decrease, large_data_opt, large_right, right_height_decrease) =
          split large key ~compare
        in
        let left_opt =
          match large_left with
          | None -> Some (small_left, small_left_height)
          | Some large_left ->
            xor'
              small_left
              small_left_height
              large_left
              (large_height - left_height_decrease)
              ~compare
        in
        let right_opt =
          match large_right with
          | None -> Some (small_right, small_right_height)
          | Some large_right ->
            xor'
              small_right
              small_right_height
              large_right
              (large_height - right_height_decrease)
              ~compare
        in
        match left_opt, right_opt with
        | None, None -> None
        | Some (t, height), None | None, Some (t, height) ->
          (match large_data_opt with
           | None -> Some (t, height)
           | Some _ ->
             remove' t key ~compare
             |> Option.map ~f:(fun (t, height_decreased) ->
               (t, height + Height_decrease.to_int height_decreased)))
        | Some (left, left_height), Some (right, right_height) ->
          (match large_data_opt with
           | None -> Some (join left left_height key new_data right right_height)
           | Some _ -> Some (join0 left left_height right right_height))
    ;;

    let xor map1 map2 ~compare =
      xor' map1 (height map1) map2 (height map2) ~compare
      |> Option.map ~f:fst
    ;;

    let remove_set _ = failwith "unimpl"
    let restrict_to_set _ = failwith "unimpl"

    let rec to_sequence_gen map =
      let open Sequence.Generator.Let_syntax in
      let yield = Sequence.Generator.yield in
      match map with
      | Leaf1 (key, data) ->
        yield (key, data)
      | Leaf2 (key1, data1, key2, data2) ->
        let%bind () = yield (key1, data1) in
        yield (key2, data2)
      | Two (left, key, data, right)
      | OneTwo (left, key, data, right)
      | TwoOne (left, key, data, right)
        ->
        let%bind () = to_sequence_gen left in
        let%bind () = yield (key, data) in
        to_sequence_gen right
    ;;

    let to_sequence map = Sequence.Generator.run (to_sequence_gen map)

    let of_potentially_empty_queue queue =
      if Queue.is_empty queue
      then None
      else Some (of_sorted_array_unchecked (Queue.to_array queue))

    let filter_mapi map ~f =
      let queue = Queue.create () in
      iteri map ~f:(fun ~key ~data ->
        match f ~key ~data with
        | None -> ()
        | Some data -> Queue.enqueue queue (key, data));
      of_potentially_empty_queue queue
    ;;

    let rec iter2' seq1 seq2 ~f ~compare =
      match Sequence.next seq1, Sequence.next seq2 with
      | None, None -> ()
      | Some _, None -> Sequence.iter seq1 ~f:(fun (key, data) -> f ~key (`Left data))
      | None, Some _ -> Sequence.iter seq2 ~f:(fun (key, data) -> f ~key (`Right data))
      | Some ((key1, data1), seq1'), Some ((key2, data2), seq2') ->
        match do_compare compare key1 key2 with
        | Less -> f ~key:key1 (`Left data1); iter2' seq1' seq2 ~f ~compare
        | Equal -> f ~key:key1 (`Both (data1, data2)); iter2' seq1' seq2' ~f ~compare
        | Greater -> f ~key:key2 (`Right data2); iter2' seq1 seq2' ~f ~compare

    let iter2 map1 map2 ~f ~compare =
      iter2' (to_sequence map1) (to_sequence map2) ~f ~compare
    ;;

    let generic_merge map1 map2 ~merge ~compare =
      let queue = Queue.create () in
      iter2 map1 map2 ~compare ~f:(fun ~key data ->
        match merge ~key data with
        | None -> ()
        | Some data -> Queue.enqueue queue (key, data));
      of_potentially_empty_queue queue
    ;;
  end

  type ('k, 'v, 'cmp) t = ('k, 'v) Balanced_tree2.t [@@deriving sexp_of]

  let height = Balanced_tree.height
  let length = Balanced_tree.length

  let empty = Balanced_tree.empty
  let is_empty = Balanced_tree.is_empty
  let of_non_empty = Balanced_tree.of_non_empty
  let of_non_empty_option = Balanced_tree.of_non_empty_option
  let get_non_empty = Balanced_tree.get_non_empty
  let get_non_empty_exn = Balanced_tree.get_non_empty_exn

  let singleton ~key ~data = Balanced_tree.singleton key data

  let of_sorted_balanced_tree_unchecked balanced_tree = balanced_tree

  let of_sorted_balanced_tree_exn balanced_tree ~compare =
    match balanced_tree with
    | None -> None
    | Some non_empty_balanced_tree ->
      Some (Non_empty.of_sorted_balanced_tree_exn non_empty_balanced_tree ~compare)
  ;;

  let to_balanced_tree t = t

  let of_sorted_array_unchecked array =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_sorted_array_unchecked array)
  ;;

  let of_sorted_array_exn array ~compare =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_sorted_array_exn array ~compare)
  ;;

  let of_array array ~compare =
    if Array.is_empty array
    then None
    else Some (Non_empty.of_array array ~compare)
  ;;

  let of_sorted_list_unchecked list =
    if List.is_empty list
    then None
    else Some (Non_empty.of_sorted_list_unchecked list)
  ;;

  let of_sorted_list_exn list ~compare =
    if List.is_empty list
    then None
    else Some (Non_empty.of_sorted_list_exn list ~compare)
  ;;

  let of_list list ~compare =
    if List.is_empty list
    then None
    else Some (Non_empty.of_list list ~compare)
  ;;

  let to_list = Balanced_tree.to_pair_list
  let keys = Balanced_tree.to_list1
  let key_set = Balanced_tree.to_tree1
  let data = Balanced_tree.to_list2
  let map t ~f = Balanced_tree.map2 t ~f
  let iter = Balanced_tree.iter2
  let iteri t ~f = Balanced_tree.iter_both t ~f:(fun key data -> f ~key ~data)
  let fold = Balanced_tree.fold2
  let foldi t ~init ~f = Balanced_tree.fold_both t ~init ~f:(fun acc key data -> f acc ~key ~data)
  let fold_right = Balanced_tree.fold2_right
  let fold_righti t ~init ~f = Balanced_tree.fold_both_right t ~init ~f:(fun key data acc -> f ~key ~data acc)
  let fold_map = Balanced_tree.fold_map2
  let fold_mapi t ~init ~f =
    Balanced_tree.fold_map_both t ~init ~f:(fun acc key data ->
      let (acc, data) = f acc ~key ~data in
      acc, key, data)
  ;;

  let rekeying_map t ~f ~compare =
    match t with
    | None -> None
    | Some non_empty -> Some (Non_empty.rekeying_map non_empty ~f ~compare)
  ;;

  let find_and_call t key ~if_found ~if_not_found ~compare =
    match t with
    | None -> if_not_found ()
    | Some non_empty -> Non_empty.find_and_call non_empty key ~if_found ~if_not_found ~compare
  ;;

  let find t key ~compare =
    match t with
    | None -> None
    | Some non_empty -> Non_empty.find non_empty key ~compare
  ;;

  let find_exn t key ~compare =
    Non_empty.find_exn (get_non_empty_exn t) key ~compare
  ;;

  let mem t key ~compare =
    match t with
    | None -> false
    | Some non_empty -> Non_empty.mem non_empty key ~compare

  let add_non_empty t ~key ~data ~compare =
    match t with
    | None -> `Ok (Non_empty.singleton ~key ~data)
    | Some non_empty -> Non_empty.add non_empty ~key ~data ~compare
  ;;

  let add t ~key ~data ~compare =
    match add_non_empty t ~key ~data ~compare with
    | `Duplicate_key -> `Duplicate_key
    | `Ok non_empty -> `Ok (Some non_empty)
  ;;

  let add_non_empty_exn t ~key ~data ~compare =
    match t with
    | None -> Non_empty.singleton ~key ~data
    | Some non_empty -> Non_empty.add_exn non_empty ~key ~data ~compare
  ;;

  let add_exn t ~key ~data ~compare =
    Some (add_non_empty_exn t ~key ~data ~compare)
  ;;

  let set_non_empty t ~key ~data ~compare =
    match t with
    | None -> Non_empty.singleton ~key ~data
    | Some non_empty -> Non_empty.set non_empty ~key ~data ~compare
  ;;

  let set t ~key ~data ~compare =
    Some (set_non_empty t ~key ~data ~compare)
  ;;

  let generic_add_non_empty t ~key ~data ~on_already_present ~compare =
    match t with
    | None -> Non_empty.singleton ~key ~data
    | Some non_empty -> Non_empty.generic_add non_empty ~key ~data ~on_already_present ~compare
  ;;

  let generic_add t ~key ~data ~on_already_present ~compare =
    Some (generic_add_non_empty t ~key ~data ~on_already_present ~compare)
  ;;

  let remove t key ~compare =
    match t with
    | None -> None
    | Some non_empty -> Non_empty.remove non_empty key ~compare
  ;;

  let find_and_remove t key ~compare =
    match t with
    | None -> None, t
    | Some non_empty ->
      match Non_empty.find_and_remove non_empty key ~compare with
      | None -> None, t
      | Some (data, t) -> Some data, t
  ;;

  let union map1 map2 ~merge ~compare =
    match (map1, map2) with
    | (None, None) -> None
    | (Some non_empty, None) | (None, Some non_empty) -> Some non_empty
    | (Some non_empty1, Some non_empty2) ->
      Some (Non_empty.union non_empty1 non_empty2 ~merge ~compare)
  ;;

  let inter map1 map2 ~merge ~compare =
    match (map1, map2) with
    | (None, _) | (_, None) -> None
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.inter non_empty1 non_empty2 ~merge ~compare
  ;;

  let xor map1 map2 ~compare =
    match (map1, map2) with
    | (None, None) -> None
    | (None, map) | (map, None) -> map
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.xor non_empty1 non_empty2 ~compare
  ;;

  let remove_set map set ~compare =
    match (map, set) with
    | (_, None) -> map
    | (None, _) -> None
    | (Some non_empty_map, Some non_empty_set) ->
      Non_empty.remove_set non_empty_map non_empty_set ~compare
  ;;

  let restrict_to_set map set ~compare =
    match (map, set) with
    | (None, _) | (_, None) -> None
    | (Some non_empty_map, Some non_empty_set) ->
      Non_empty.restrict_to_set non_empty_map non_empty_set ~compare
  ;;

  (* CR wduff: This should probably move into the unordered part. *)
  let filter_mapi t ~f =
    match t with
    | None -> None
    | Some non_empty -> Non_empty.filter_mapi non_empty ~f
  ;;

  let generic_merge map1 map2 ~merge ~compare =
    match (map1, map2) with
    | (None, None) -> None
    | (Some non_empty, None) ->
      Non_empty.filter_mapi non_empty ~f:(fun ~key ~data -> merge ~key (`Left data))
    | (None, Some non_empty) ->
      Non_empty.filter_mapi non_empty ~f:(fun ~key ~data -> merge ~key (`Right data))
    | (Some non_empty1, Some non_empty2) ->
      Non_empty.generic_merge non_empty1 non_empty2 ~merge ~compare
  ;;

  let find_min t =
    Option.map t ~f:Non_empty.find_min
  ;;

  let find_max t =
    Option.map t ~f:Non_empty.find_max
  ;;

  let find_min_exn t =
    get_non_empty_exn t
    |> Non_empty.find_min
  ;;

  let find_max_exn t =
    get_non_empty_exn t
    |> Non_empty.find_max
  ;;

  let remove_min t =
    Option.bind t ~f:Non_empty.remove_min
  ;;

  let remove_max t =
    Option.bind t ~f:Non_empty.remove_max
  ;;

  let find_and_remove_min t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (min, t) = Non_empty.find_and_remove_min non_empty in
      (Some min, t)
  ;;

  let find_and_remove_max t =
    match t with
    | None -> (None, t)
    | Some non_empty ->
      let (max, t) = Non_empty.find_and_remove_max non_empty in
      (Some max, t)
  ;;

  module type Specialized =
    Specialized_map
    with type ('a, 'b) balanced_tree := ('a, 'b) Balanced_tree2.t
    with type ('a, 'b) non_empty_balanced_tree := ('a, 'b) Balanced_tree2.Non_empty.t
    with type ('k, 'v, 'cmp) generic_map := ('k, 'v, 'cmp) t
    with type ('k, 'v, 'cmp) non_empty_generic_map := ('k, 'v, 'cmp) Non_empty.t

  module Make_using_comparator (Key : Comparator) : Specialized
    with type key = Key.t
    with type compare_witness = Key.compare_witness
    with type set = (Key.t, Key.compare_witness) Set.t
    with type non_empty_set = (Key.t, Key.compare_witness) Set.Non_empty.t
  =
  struct
    type key = Key.t [@@deriving sexp_of]
    type compare_witness = Key.compare_witness
    let sexp_of_compare_witness = [%sexp_of: _]
    type set = (Key.t, compare_witness) Set.t
    type non_empty_set = (Key.t, compare_witness) Set.Non_empty.t

    let compare = Key.compare

    type nonrec 'a t = (key, 'a, compare_witness) t [@@deriving sexp_of]

    module Non_empty
      : Specialized_non_empty_map
        with type set := (Key.t, compare_witness) Set.Non_empty.t
        with type ('a, 'b) balanced_tree := ('a, 'b) Balanced_tree2.Non_empty.t
        with type ('k, 'v, 'cmp) generic_map := ('k, 'v, 'cmp) Non_empty.t
        with type 'a maybe_empty := 'a t
        with type key = key
        with type compare_witness = compare_witness
    =
    struct
      type nonrec key = key [@@deriving sexp_of]
      type nonrec compare_witness = compare_witness [@@deriving sexp_of]

      let compare = Key.compare

      type 'a t = (key, 'a, compare_witness) Non_empty.t [@@deriving sexp_of]

      let height = Non_empty.height
      let length = Non_empty.length
      let singleton = Non_empty.singleton
      let of_array = Non_empty.of_array ~compare
      let of_sorted_array_unchecked = Non_empty.of_sorted_array_unchecked
      let of_sorted_array_exn = Non_empty.of_sorted_array_exn ~compare
      let of_list = Non_empty.of_list ~compare
      let of_sorted_list_unchecked = Non_empty.of_sorted_list_unchecked
      let of_sorted_list_exn = Non_empty.of_sorted_list_exn ~compare
      let of_sorted_balanced_tree_unchecked = Non_empty.of_sorted_balanced_tree_unchecked
      let of_sorted_balanced_tree_exn = Non_empty.of_sorted_balanced_tree_exn ~compare
      let to_balanced_tree = Non_empty.to_balanced_tree
      let to_list = Non_empty.to_list
      let keys = Non_empty.keys
      let key_set = Non_empty.key_set
      let data = Non_empty.data
      let map = Non_empty.map
      let iter = Non_empty.iter
      let iteri = Non_empty.iteri
      let fold = Non_empty.fold
      let foldi = Non_empty.foldi
      let fold_right = Non_empty.fold_right
      let fold_righti = Non_empty.fold_righti
      let fold_map = Non_empty.fold_map
      let fold_mapi = Non_empty.fold_mapi
      let rekeying_map' = Non_empty.rekeying_map
      let rekeying_map = Non_empty.rekeying_map ~compare
      let find = Non_empty.find ~compare
      let find_exn = Non_empty.find_exn ~compare
      let mem = Non_empty.mem ~compare
      let find_and_call = Non_empty.find_and_call ~compare
      let add = Non_empty.add ~compare
      let add_exn = Non_empty.add_exn ~compare
      let set = Non_empty.set ~compare
      let set' = Non_empty.set' ~compare
      let generic_add = Non_empty.generic_add ~compare
      let remove = Non_empty.remove ~compare
      let find_and_remove = Non_empty.find_and_remove ~compare
      let join_into_left = Non_empty.join_into_left
      let join_into_right = Non_empty.join_into_right
      let join = Non_empty.join
      let join0 = Non_empty.join0
      let split = Non_empty.split ~compare
      let union = Non_empty.union ~compare
      let inter = Non_empty.inter ~compare
      let xor = Non_empty.xor ~compare
      let remove_set = Non_empty.remove_set ~compare
      let restrict_to_set = Non_empty.restrict_to_set ~compare
      let filter_mapi = Non_empty.filter_mapi
      let generic_merge = Non_empty.generic_merge ~compare
      let find_min = Non_empty.find_min
      let remove_min = Non_empty.remove_min
      let find_and_remove_min = Non_empty.find_and_remove_min
      let find_max = Non_empty.find_max
      let remove_max = Non_empty.remove_max
      let find_and_remove_max = Non_empty.find_and_remove_max
    end

    let height = height
    let length = length
    let empty = empty
    let is_empty = is_empty
    let of_non_empty = of_non_empty
    let of_non_empty = of_non_empty
    let of_non_empty_option = of_non_empty_option
    let get_non_empty = get_non_empty
    let get_non_empty_exn = get_non_empty_exn
    let singleton = singleton
    let of_array = of_array ~compare
    let of_sorted_array_unchecked = of_sorted_array_unchecked
    let of_sorted_array_exn = of_sorted_array_exn ~compare
    let of_list = of_list ~compare
    let of_sorted_list_unchecked = of_sorted_list_unchecked
    let of_sorted_list_exn = of_sorted_list_exn ~compare
    let of_sorted_balanced_tree_unchecked = of_sorted_balanced_tree_unchecked
    let of_sorted_balanced_tree_exn = of_sorted_balanced_tree_exn ~compare
    let to_balanced_tree = to_balanced_tree
    let to_list = to_list
    let keys = keys
    let key_set = key_set
    let data = data
    let map = map
    let iter = iter
    let iteri = iteri
    let fold = fold
    let foldi = foldi
    let fold_right = fold_right
    let fold_righti = fold_righti
    let fold_map = fold_map
    let fold_mapi = fold_mapi
    let rekeying_map' = rekeying_map
    let rekeying_map = rekeying_map ~compare
    let find = find ~compare
    let find_exn = find_exn ~compare
    let mem = mem ~compare
    let find_and_call = find_and_call ~compare
    let add = add ~compare
    let add_exn = add_exn ~compare
    let set = set ~compare
    let generic_add = generic_add ~compare
    let add_non_empty = add_non_empty ~compare
    let add_non_empty_exn = add_non_empty_exn ~compare
    let set_non_empty = set_non_empty ~compare
    let generic_add_non_empty = generic_add_non_empty ~compare
    let remove = remove ~compare
    let find_and_remove = find_and_remove ~compare
    let union = union ~compare
    let inter = inter ~compare
    let xor = xor ~compare
    let remove_set = remove_set ~compare
    let restrict_to_set = restrict_to_set ~compare
    let filter_mapi = filter_mapi
    let generic_merge = generic_merge ~compare
    let find_min = find_min
    let find_min_exn = find_min_exn
    let remove_min = remove_min
    let find_and_remove_min = find_and_remove_min
    let find_max = find_max
    let find_max_exn = find_max_exn
    let remove_max = remove_max
    let find_and_remove_max = find_and_remove_max
  end

  module Make (Key : Comparable) = Make_using_comparator (struct include Key include Compare.Make (Key) end)
end
