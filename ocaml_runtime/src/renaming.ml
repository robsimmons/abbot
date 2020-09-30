open! Core

module type S = sig
  type t

  val apply : t -> Internal_var.t -> Internal_var.t

  val bind : Temp.t -> t
  val bind' : Temp.t list -> t

  val unbind : Temp.t -> t
  val unbind' : Temp.t list -> t

  val ident : t
  val compose : t -> t -> t
end

let raise_not_fresh var =
  raise_s
    [%message
      "Internal abbot bug. Variable passed to [unbind] was not fresh."
        (var : Temp.t)]
;;

module Function = struct
  type t = Internal_var.t -> Internal_var.t

  let apply t = t

  let ident var = var

  let compose t1 t2 var = t1 (t2 var)

  let bind free_var : t = function
    | Bound_var bound_var -> Bound_var (bound_var + 1)
    | Free_var free_var' ->
      match Temp.equal free_var free_var' with
      | true -> Bound_var 0
      | false -> Free_var free_var'
  ;;

  let bind' free_vars =
    List.fold free_vars ~init:ident ~f:(fun acc free_var ->
      compose (bind free_var) acc)
  ;;

  let unbind free_var : t = function
    | Free_var free_var' ->
      (match Temp.equal free_var free_var' with
       | false -> Free_var free_var'
       | true -> raise_not_fresh free_var)
    | Bound_var bound_var ->
      match bound_var with
      | 0 -> Free_var free_var
      | _ -> Bound_var (bound_var - 1)
  ;;

  let unbind' free_vars =
    List.fold free_vars ~init:ident ~f:(fun acc free_var -> compose acc (unbind free_var))
  ;;

  let shift : t = function
    | Free_var free_var -> Free_var free_var
    | Bound_var bound_var -> Bound_var (bound_var + 1)
  ;;

  let weaken (t : t) : t = function
    | Free_var free_var -> shift (t (Free_var free_var))
    | Bound_var bound_var ->
      match bound_var with
      | 0 -> Bound_var 0
      | _ -> shift (t (Bound_var (bound_var - 1)))
  ;;

  (* We don't actually need [weaken] or [shift], but they are useful references. *)
  let _ = weaken
end

module Function2 = struct
  type t =
    | Ident
    | Fun of (Internal_var.t -> Internal_var.t)

  let apply = function
    | Ident -> ident
    | Fun f -> f

  let ident = Ident

  let compose t1 t2 =
    match (t1, t2) with
    | Ident, t | t, Ident -> t
    | Fun f1, Fun f2 -> Fun (fun var -> f1 (f2 var))
  ;;

  let bind free_var : t =
    Fun (function
      | Bound_var bound_var -> Bound_var (bound_var + 1)
      | Free_var free_var' ->
        match Temp.equal free_var free_var' with
        | true -> Bound_var 0
        | false -> Free_var free_var')
  ;;

  let bind' free_vars =
    List.fold free_vars ~init:ident ~f:(fun acc free_var ->
      compose (bind free_var) acc)
  ;;

  let unbind free_var : t =
    Fun (function
      | Free_var free_var' ->
        (match Temp.equal free_var free_var' with
         | false -> Free_var free_var'
         | true -> raise_not_fresh free_var)
      | Bound_var bound_var ->
        match bound_var with
        | 0 -> Free_var free_var
        | _ -> Bound_var (bound_var - 1))
  ;;

  let unbind' free_vars =
    List.fold free_vars ~init:ident ~f:(fun acc free_var -> compose acc (unbind free_var))
  ;;
end

(* Facts:

   apply ident x = x
   apply (compose t1 t2) x = apply t1 (apply t2 x)

   compose t1 (compose t2 t3) = compose (compose t1 t2) t3
   compose t ident = t = compose ident t

   bind' [] = ident
   bind' [ x ] = bind x
   bind' (x :: xs) = compose (bind' xs) (bind x)
   bind' (l @ r) = compose (bind' r) (bind' l)

   unbind' [] = ident
   unbind' [ x ] = unbind x
   unbind' (x :: xs) = compose (unbind x) (unbind' xs)
   unbind' (l @ r) = compose (unbind' l) (unbind' r)

   compose (unbind x) (bind x) = ident

   compose (bind x) (unbind x) is not the identity because
   compose (bind x) (unbind x) (Free_var x) raises,
   but it is the identity if x is "fresh".

   compose (unbind x) (weaken t) = compose acc (unbind x)
   iff t (Free_var x) = Free_var x
*)

module Map_and_array : S = struct
  module Set = Temp.Brother_tree_set
  module Map = Temp.Brother_tree_map
  (*
  module Set = Temp.Set
  module Map = Temp.Map
  *)

  module T : sig
    (* A [t] consists of three field to deal with three sets of variables.
       - Free variables are mapped according to [t.free_vars]. Free variables outside the domain of
         the map are unchanged.
       - Bound variables less than [List.length t.initial_bound_vars] are mapped by indexing into
         t.initial_bound_vars.
       - Bound variable greater than or equal to [List.length t.initial_bound_vars] are mapped as
         [n] => [n - List.length t.initial_bound_vars + t.shift].

       Blacklist is used so that we can raise if we discover that a free variable passed to unbind
       was not fresh. *)
    type t = private
      { free_vars : Internal_var.t Map.t
      ; blacklist : Set.t
      ; initial_bound_vars : Internal_var.t array
      ; shift : int
      }
    [@@deriving fields, sexp_of]

    val create
      :  free_vars:Internal_var.t Map.t
      -> blacklist:Set.t
      -> initial_bound_vars:Internal_var.t array
      -> shift:int
      -> t
  end = struct
    type t =
      { free_vars : Internal_var.t Map.t
      ; blacklist : Set.t
      ; initial_bound_vars : Internal_var.t array
      ; shift : int
      }
    [@@deriving fields, sexp_of]

    let debug = false

    let invariant' { free_vars; blacklist; initial_bound_vars; shift } =
      begin
        let overlap = Set.inter (Map.key_set free_vars) blacklist in
        match Set.is_empty overlap with
        | true -> ()
        | false ->
          raise_s [%message "blacklist overlaps with free variable mapping" (overlap : Set.t)]
      end;
      begin
        match shift >= 0 with
        | true -> ()
        | false -> raise_s [%message "negative shift"]
      end;
      Map.iteri free_vars ~f:(fun ~key:fv1 ~data ->
        match data with
        | Free_var fv2 when Temp.equal fv1 fv2 ->
          raise_s [%message "superfluous identity mapping"]
        | _ -> ());
      begin
        match initial_bound_vars.(Array.length initial_bound_vars - 1) with
        | Bound_var bound_var when bound_var = shift - 1 ->
          raise_s [%message "superfluous bound var mapping"]
        | _ -> ()
      end;
      begin
        (* Check for duplicate outputs. *)
        let min_shift_output = shift in
        let other_outputs =
          Map.data free_vars
          @ Array.to_list initial_bound_vars
        in
        List.iter other_outputs ~f:(function
          | Bound_var bv when bv >= min_shift_output ->
            raise_s [%message "duplicate output"]
          | _ -> ());
        match List.find_a_dup other_outputs ~compare:Internal_var.compare with
        | None -> ()
        | Some _ -> raise_s [%message "duplicate output"]
      end
    ;;

    let invariant t =
      try invariant' t
      with error ->
        raise_s [%message "Invariant check failed." (error : exn) (t : t)]

    let create ~free_vars ~blacklist ~initial_bound_vars ~shift =
      let t = { free_vars; blacklist; initial_bound_vars; shift } in
      if debug then invariant t;
      t
  end

  include T

  let apply t (var : Internal_var.t) : Internal_var.t =
    match var with
    | Free_var free_var ->
      (match Set.mem t.blacklist free_var with
       | false -> ()
       | true -> raise_not_fresh free_var);
      (match Map.find t.free_vars free_var with
       | Some result -> result
       | None -> Free_var free_var)
    | Bound_var bound_var ->
      let len = Array.length t.initial_bound_vars in
      match bound_var < len with
      | true -> t.initial_bound_vars.(bound_var)
      | false -> Bound_var (bound_var - len + t.shift)
  ;;

  let ident =
    create ~free_vars:Map.empty ~blacklist:Set.empty ~initial_bound_vars:[||] ~shift:0
  ;;

  (* CR wduff: Better error messages. *)
  let check_less elt1 elt2 ~compare =
    match Brother_tree_intf.Compare.do_compare compare elt1 elt2 with
    | Less -> ()
    | Equal -> raise_s [%message "duplicate element"]
    | Greater -> raise_s [%message "elements out of order"]
  ;;

  let rec foo' map1 height1 map2 height2 ~f =
    let map2 =
      Map.Non_empty.to_balanced_tree map2
      |> Brother_tree.Balanced_tree2.Non_empty.to_raw_tree
    in
    match map2 with
    | Leaf1 (key, data) ->
      let (t, height_increased) = Map.Non_empty.set' map1 ~key ~data:(f data) in
      (t, height1 + Brother_tree_intf.Height_increase.to_int height_increased)
    | Leaf2 (key1, data1, key2, data2) ->
      let (t, height_increased1) = Map.Non_empty.set' map1 ~key:key1 ~data:(f data1) in
      let (t, height_increased2) = Map.Non_empty.set' t ~key:key2 ~data:(f data2) in
      (t, height1 + Brother_tree_intf.Height_increase.to_int height_increased1 + Brother_tree_intf.Height_increase.to_int height_increased2)
    | Two (left2, key, data, right2)
    | OneTwo (left2, key, data, right2)
    | TwoOne (left2, key, data, right2)
      ->
      let (left2_height, right2_height) =
        match map2 with
        | Two _ -> (height2 - 1, height2 - 1)
        | OneTwo _ -> (height2 - 2, height2 - 1)
        | TwoOne _ -> (height2 - 1, height2 - 2)
        | _ -> assert false
      in
      (* CR wduff: We could avoid this unsafety if there was some kind of "view" type that kept the
         sub-maps as maps, but exposed the variant. Maybe that's overkill. *)
      let left2 =
        Brother_tree.Balanced_tree2.Non_empty.of_balanced_raw_tree_unchecked left2
        |> Map.Non_empty.of_sorted_balanced_tree_unchecked
      in
      let right2 =
        Brother_tree.Balanced_tree2.Non_empty.of_balanced_raw_tree_unchecked right2
        |> Map.Non_empty.of_sorted_balanced_tree_unchecked
      in
      let (left1, left1_height_decrease, _, right1, right1_height_decrease) =
        Map.Non_empty.split map1 key
      in
      let left, left_height =
        match Map.get_non_empty left1 with
        | None -> (Map.Non_empty.map left2 ~f, left2_height)
        | Some left1 ->
          foo'
            left1
            (height1 - left1_height_decrease)
            left2
            left2_height
            ~f
      in
      let right, right_height =
        match Map.get_non_empty right1 with
        | None -> (Map.Non_empty.map right2 ~f, right2_height)
        | Some right1 ->
          foo'
            right1
            (height1 - right1_height_decrease)
            right2
            right2_height
            ~f
      in
      Map.Non_empty.join left left_height key (f data) right right_height
  ;;

  let foo map1 map2 ~f =
    match (Map.get_non_empty map1, Map.get_non_empty map2) with
    | (None, None) -> Map.empty
    | (Some non_empty, None) -> Map.of_non_empty non_empty
    | (None, Some non_empty) -> Map.of_non_empty (Map.Non_empty.map non_empty ~f)
    | (Some non_empty1, Some non_empty2) ->
      let (non_empty, _) =
        foo'
          non_empty1
          (Map.Non_empty.height non_empty1)
          non_empty2
          (Map.Non_empty.height non_empty2)
          ~f
      in
      Map.of_non_empty non_empty
  ;;

  let to_raw map =
    Map.to_balanced_tree map
    |> Brother_tree.Balanced_tree2.to_raw_tree
  ;;

  let compose t1 t2 =
    let free_vars =
      (*let x =*)
        foo t1.free_vars t2.free_vars ~f:(apply t1)
    (*in
      let y =
        let t2_free_vars' = Map.map t2.free_vars ~f:(apply t1) in
        Map.union t1.free_vars t2_free_vars' ~merge:(fun ~key:_ _ d2 -> d2)
      in
      let z =
        Map.foldi t2.free_vars ~init:t1.free_vars ~f:(fun acc ~key ~data ->
          Map.set acc ~key ~data:(apply t1 data))
      in
      if not (List.equal [%compare.equal: Temp.t * Internal_var.t] (Map.to_list x) (Map.to_list y))
      || not (List.equal [%compare.equal: Temp.t * Internal_var.t] (Map.to_list y) (Map.to_list z))
      then
        raise_s
          [%message
            ""
              (to_raw t1.free_vars : (Temp.t, Internal_var.t) Brother_tree.Tree2.t)
              (to_raw t2.free_vars : (Temp.t, Internal_var.t) Brother_tree.Tree2.t)
              (to_raw x : (Temp.t, Internal_var.t) Brother_tree.Tree2.t)
              (to_raw y : (Temp.t, Internal_var.t) Brother_tree.Tree2.t)
              (to_raw z : (Temp.t, Internal_var.t) Brother_tree.Tree2.t)];
      x*)
(*
      Map.merge t1.free_vars t2.free_vars ~f:(fun ~key data ->
        let result =
          match data with
          | `Left result ->
            (match Set.mem t2.blacklist key with
             | true -> None
             | false -> Some result)
          | `Right result | `Both (_, result) ->
            Some (apply t1 result)
        in
        match result with
        | Some (Free_var fv) when Temp.equal fv key -> None
        | _ -> result)
*)
    in
    (* let blacklist = Set.union (Set.diff t1.blacklist (Map.key_set t2.free_vars)) t2.blacklist in *)
    let (initial_bound_vars, shift) =
      let length_of_initial_bound_vars1 = Array.length t1.initial_bound_vars in
      let length_of_initial_bound_vars2 = Array.length t2.initial_bound_vars in
      match length_of_initial_bound_vars1 <= t2.shift with
      | true ->
        (Array.map t2.initial_bound_vars ~f:(apply t1),
         t1.shift + t2.shift - length_of_initial_bound_vars1)
      | false ->
        let num_initial_bound_vars =
          length_of_initial_bound_vars2 + length_of_initial_bound_vars1 - t2.shift
        in
        let initial_bound_vars =
          Array.init num_initial_bound_vars ~f:(fun i ->
            if i < length_of_initial_bound_vars2
            then apply t1 t2.initial_bound_vars.(i)
            else t1.initial_bound_vars.(i + t2.shift))
        in
        (initial_bound_vars, t1.shift)
    in
    (* CR wduff: Can we avoid ever creating the extra array? Or do so more lazily? How often does
       this even happen? *)
    let drop_count = ref 0 in
    let shift = ref shift in
    while
      !drop_count < Array.length initial_bound_vars
      &&
      (match initial_bound_vars.(Array.length initial_bound_vars - !drop_count - 1) with
       | Bound_var bound_var when bound_var = !shift - 1 -> true
       | _ -> false)
    do
      incr drop_count;
      decr shift;
    done;
    let initial_bound_vars =
      if !drop_count = 0
      then initial_bound_vars
      else Array.sub initial_bound_vars ~pos:0 ~len:(Array.length initial_bound_vars - !drop_count)
    in
    create ~free_vars ~blacklist:Set.empty ~initial_bound_vars ~shift:!shift
  ;;

  let bind' free_vars =
    let num_new_bound_vars = List.length free_vars in
    let free_vars =
      (*match*)
        Array.of_list_mapi free_vars ~f:(fun i free_var -> (free_var, Internal_var.Bound_var i))
        |> Map.of_array
(*with
      | `Ok map -> map
      | `Duplicate_key duplicated_var ->
        raise_s
          [%message
            "Attempt to bind the same variable to multiple binding sites."
              (duplicated_var : Temp.t)]
*)
    in
    create ~free_vars ~blacklist:Set.empty ~initial_bound_vars:[||] ~shift:num_new_bound_vars
  ;;

  let bind free_var = bind' [ free_var ]

  let unbind' free_vars =
    let initial_bound_vars =
      Array.of_list_map free_vars ~f:(fun free_var -> Internal_var.Free_var free_var)
    in
    create
      ~free_vars:Map.empty
      ~blacklist:(Set.of_list free_vars)
      ~initial_bound_vars
      ~shift:0
  ;;

  let unbind free_var = unbind' [ free_var ]
end

(* CR wduff: Test which of these is actually faster.

   We could consider also keeping track in the abbot tree of what variables occur beneath each node.
   Then we could skip subtrees that are unaffected by a given renaming. *)
let () = ignore (module Function : S)
let () = ignore (module Function2 : S)
let () = ignore (module Map_and_array : S)
include Function2
