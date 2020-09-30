open! Core

type ('k, 'v) tree0 =
  | Empty
  | Leaf of 'k * 'v
  | Node of ('k, 'v) tree0 * 'k * 'v * ('k, 'v) tree0 * int

type ('k, 'v, 'comparator) t =
  { comparator : ('k, 'comparator) Comparator.t
  ; tree : ('k, 'v) tree0
  ; length : int
  }

(* CR wduff: This is a horrible hack. *)
module Unsafe = struct
  let expose : ('k, 'v, 'comparator) Map.t -> ('k, 'v, 'comparator) t =
    Obj.magic

  let unexpose : ('k, 'v, 'comparator) t -> ('k, 'v, 'comparator) Map.t =
    Obj.magic

  let expose_tree : ('k, 'v, 'comparator) Map.Tree.t -> ('k, 'v) tree0 =
    Obj.magic

  let unexpose_tree : ('k, 'v) tree0 -> ('k, 'v, 'comparator) Map.Tree.t =
    Obj.magic

  let _ = expose
  let _ = unexpose
  let _ = expose_tree
  let _ = unexpose_tree
end

module Tree_operations = struct
  let height = function
    | Empty -> 0
    | Leaf _ -> 1
    | Node (_, _, _, _, h) -> h
  ;;

  let create l x d r =
    let hl = height l
    and hr = height r in
    if hl = 0 && hr = 0
    then Leaf (x, d)
    else Node (l, x, d, r, if hl >= hr then hl + 1 else hr + 1)
  ;;

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2
    then (
      match l with
      | Empty -> invalid_arg "Map.bal"
      | Leaf _ -> assert false (* height(Leaf) = 1 && 1 is not larger than hr + 2 *)
      | Node (ll, lv, ld, lr, _) ->
        if height ll >= height lr
        then create ll lv ld (create lr x d r)
        else (
          match lr with
          | Empty -> invalid_arg "Map.bal"
          | Leaf (lrv, lrd) ->
            create (create ll lv ld Empty) lrv lrd (create Empty x d r)
          | Node (lrl, lrv, lrd, lrr, _) ->
            create (create ll lv ld lrl) lrv lrd (create lrr x d r)))
    else if hr > hl + 2
    then (
      match r with
      | Empty -> invalid_arg "Map.bal"
      | Leaf _ -> assert false (* height(Leaf) = 1 && 1 is not larger than hl + 2 *)
      | Node (rl, rv, rd, rr, _) ->
        if height rr >= height rl
        then create (create l x d rl) rv rd rr
        else (
          match rl with
          | Empty -> invalid_arg "Map.bal"
          | Leaf (rlv, rld) ->
            create (create l x d Empty) rlv rld (create Empty rv rd rr)
          | Node (rll, rlv, rld, rlr, _) ->
            create (create l x d rll) rlv rld (create rlr rv rd rr)))
    else create l x d r
  ;;

  let rec set t key data ~compare_key
    =
    match t with
    | Empty -> Leaf (key, data)
    | Leaf (v, d) ->
      let c = compare_key key v in
      if c = 0
      then Leaf (key, data)
      else if c < 0
      then Node (Leaf (key, data), v, d, Empty, 2)
      else Node (Empty, v, d, Leaf (key, data), 2)
    | Node (l, v, d, r, h) ->
      let c = compare_key key v in
      if c = 0
      then Node (l, key, data, r, h)
      else if c < 0
      then (
        let l = set l key data ~compare_key in
        bal l v d r)
      else (
        let r = set r key data ~compare_key in
        bal l v d r)
  ;;

  let rec join l k d r ~compare_key =
    match l, r with
    | Empty, _ -> set r k d ~compare_key
    | _, Empty -> set l k d ~compare_key
    | Leaf (lk, ld), _ -> set (set r k d ~compare_key) lk ld ~compare_key
    | _, Leaf (rk, rd) -> set (set l k d ~compare_key) rk rd ~compare_key
    | Node (ll, lk, ld, lr, lh), Node (rl, rk, rd, rr, rh) ->
      (* [bal] requires height difference <= 3. *)
      if lh > rh + 3
      (* [height lr >= height r],
         therefore [height (join lr k d r ...)] is [height rl + 1] or [height rl]
         therefore the height difference with [ll] will be <= 3 *)
      then bal ll lk ld (join lr k d r ~compare_key)
      else if rh > lh + 3
      then bal (join l k d rl ~compare_key) rk rd rr
      else bal l k d r
  ;;
end

let join l k d r =
  let l = Unsafe.expose l in
  let r = Unsafe.expose r in
  let comparator = l.comparator in
  let length = l.length + 1 + r.length  in
  let tree =
    Tree_operations.join l.tree k d r.tree ~compare_key:comparator.compare
  in
  Unsafe.unexpose { comparator; tree; length }
;;

let join0 l r =
  if Map.length l > Map.length r
  then begin
    match Map.max_elt l with
    | None -> r
    | Some (k, d) ->
      join (Map.remove l k) k d r
  end
  else begin
    match Map.min_elt r with
    | None -> l
    | Some (k, d) ->
      join l k d (Map.remove r k)
  end
;;

let choose_key map =
  match (Unsafe.expose map).tree with
  | Empty -> None
  | Leaf (k, _) -> Some k
  | Node (_, k, _, _, _) -> Some k
;;

let rec remove_set map set =
  let key =
    if Map.length map < Set.length set
    then choose_key map
    else Set.choose set
  in
  match key with
  | None -> map
  | Some key ->
    let (map_left, _, map_right) = Map.split map key in
    let (set_left, _, set_right) = Set.split set key in
    join0 (remove_set map_left set_left) (remove_set map_right set_right)
;;

let rec restrict_to_set map set =
  let key =
    if Map.length map < Set.length set
    then choose_key map
    else Set.choose set
  in
  match key with
  | None -> Map.Using_comparator.empty ~comparator:(Unsafe.expose map).comparator
  | Some key ->
    let (map_left, map_elt_opt, map_right) = Map.split map key in
    let (set_left, _, set_right) = Set.split set key in
    (* CR wduff: This is wrong. *)
    match map_elt_opt with
    | None ->
      join0 (restrict_to_set map_left set_left) (restrict_to_set map_right set_right)
    | Some (k, d) ->
      join (restrict_to_set map_left set_left) k d (restrict_to_set map_right set_right)
;;

let rec union' ~small ~large ~merge =
  match small with
  | Empty -> large
  | Leaf (key, data1) ->
    let data =
      match Map.find large key with
      | None -> data1
      | Some data2 -> merge ~key data1 data2
    in
    Map.set large ~key ~data
  | Node (small_left, key, data1, small_right, _) ->
    let (large_left, large_elt_opt, large_right) = Map.split large key in
    let left = union' ~small:small_left ~large:large_left ~merge in
    let right = union' ~small:small_right ~large:large_right ~merge in
    let data =
      match large_elt_opt with
      | None -> data1
      | Some (_, data2) ->
        merge ~key data1 data2
    in
    join left key data right
;;

let union map1 map2 ~merge =
  if Map.length map1 <= Map.length map2
  then union' ~small:(Unsafe.expose map1).tree ~large:map2 ~merge
  else union' ~small:(Unsafe.expose map2).tree ~large:map1 ~merge:(fun ~key x y -> merge ~key y x)
;;

let rec inter' : type k a b c cmp. small:(k, a) tree0 -> large:(k, b, cmp) Map.t -> merge:(key:k -> a -> b -> c) -> (k, c, cmp) Map.t =
  fun ~small ~large ~merge ->
  match small with
  | Empty ->
    (* CR wduff: This probably allocates, which is dumb. We can at least compute it only once. *)
    Map.Using_comparator.empty ~comparator:(Unsafe.expose large).comparator
  | Leaf (key, data1) ->
    let comparator = (Unsafe.expose large).comparator in
    (match Map.find large key with
     | None -> Map.Using_comparator.empty ~comparator
     | Some data2 -> Map.Using_comparator.singleton ~comparator key (merge ~key data1 data2))
  | Node (small_left, key, data1, small_right, _) ->
    let (large_left, large_elt_opt, large_right) = Map.split large key in
    let left = inter' ~small:small_left ~large:large_left ~merge in
    let right = inter' ~small:small_right ~large:large_right ~merge in
    match large_elt_opt with
    | None ->
      join0 left right
    | Some (_, data2) ->
      join left key (merge ~key data1 data2) right
;;

let inter map1 map2 ~merge =
  if Map.length map1 <= Map.length map2
  then inter' ~small:(Unsafe.expose map1).tree ~large:map2 ~merge
  else inter' ~small:(Unsafe.expose map2).tree ~large:map1 ~merge:(fun ~key x y -> merge ~key y x)
;;

let rec symm_diff' ~small ~large =
  match small with
  | Empty -> large
  | Leaf (key, data) ->
    if Map.mem large key
    then Map.remove large key
    else Map.set large ~key ~data
  | Node (small_left, key, data, small_right, _) ->
    let (large_left, large_elt_opt, large_right) = Map.split large key in
    let left = symm_diff' ~small:small_left ~large:large_left in
    let right = symm_diff' ~small:small_right ~large:large_right in
    match large_elt_opt with
    | None -> join left key data right
    | Some _ -> join0 left right
;;

let symm_diff map1 map2 =
  if Map.length map1 <= Map.length map2
  then symm_diff' ~small:(Unsafe.expose map1).tree ~large:map2
  else symm_diff' ~small:(Unsafe.expose map2).tree ~large:map1
;;
