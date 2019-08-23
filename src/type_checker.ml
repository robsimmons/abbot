open! Core

(* CR wduff: Check names here or in the parser to ensure that we can't run into name conflicts or
   capitalization issues in what we do in the implementation. *)

type closed_abt_typ_constraint =
  { required_to_be_closed : String.Set.t }

type unknown_abt_typ_constraint =
  { open_if_any_open : String.Set.t }

let merge_constraints_list constraints =
  List.fold_right constraints
    ~init:
      (`Unknown
         { open_if_any_open = String.Set.empty
         })
    ~f:(fun constraint1 constraint2 ->
        match (constraint1, constraint2) with
        | (`Simple _, `Open) | (`Open, `Simple _)
        | (`Simple _, `Closed _) | (`Closed _, `Simple _)
        | (`Open, `Closed _) | (`Closed _, `Open)
          ->
          (* CR wduff: Better error message. *)
          raise_s [%message "Type mismatch"]
        | (`Simple { required_to_be_closed = required_to_be_closed1 },
           `Simple { required_to_be_closed = required_to_be_closed2 })
          ->
          `Simple
            { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Simple { required_to_be_closed = required_to_be_closed1 },
           `Unknown { open_if_any_open = required_to_be_closed2 })
          ->
          `Simple { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Unknown { open_if_any_open = required_to_be_closed1 },
           `Simple { required_to_be_closed = required_to_be_closed2 })
          ->
          `Simple { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Open, `Open) -> `Open
        | (`Open, `Unknown { open_if_any_open = _ }) ->
          `Open
        | (`Unknown { open_if_any_open = _ }, `Open) ->
          `Open
        | (`Closed { required_to_be_closed = required_to_be_closed1 },
           `Closed { required_to_be_closed = required_to_be_closed2 })
          ->
          `Closed
            { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Closed { required_to_be_closed = required_to_be_closed1 },
           `Unknown { open_if_any_open = required_to_be_closed2 })
          ->
          `Closed { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Unknown { open_if_any_open = required_to_be_closed1 },
           `Closed { required_to_be_closed = required_to_be_closed2 })
          ->
          `Closed { required_to_be_closed = Set.union required_to_be_closed1 required_to_be_closed2 }
        | (`Unknown { open_if_any_open = open_if_any_open1 },
           `Unknown { open_if_any_open = open_if_any_open2 })
          ->
          `Unknown { open_if_any_open = Set.union open_if_any_open1 open_if_any_open2 })
;;

let rec check_abt ~abt_names ~symbol_names ~sort_names (abt : Parse_tree.Abt.t) =
  match abt with
  | Use (name, args) ->
    begin
      match (Map.find abt_names name, Set.mem symbol_names name, Set.mem sort_names name) with
      | (None, false, true) ->
        `Unknown { open_if_any_open = String.Set.empty }
      | (None, true, false) ->
        `Unknown { open_if_any_open = String.Set.empty }
      | (Some arity, false, false) ->
        check_simple_abt_use ~abt_names ~symbol_names ~sort_names ~name ~arity ~args
      | (None, false, false) ->
        begin
          match Builtin_abt.of_name name with
          | None -> raise_s [%message "unknown sort or abt" (name : string)]
          | Some builtin ->
            let arity = Builtin_abt.arity builtin in
            check_simple_abt_use ~abt_names ~symbol_names ~sort_names ~name ~arity ~args
        end
      | _ ->
        raise_s [%message "Abbot bug: found non-unique name" (name : string)]
    end
  | Arg_use _name ->
    (* CR wduff: Check that this is actually one of the arguments. *)
    `Simple { required_to_be_closed = String.Set.empty }
  | Prod abts ->
    List.map abts ~f:(check_abt ~abt_names ~symbol_names ~sort_names)
    |> merge_constraints_list
  | Binding name ->
    begin
      match (Set.mem symbol_names name, Set.mem sort_names name) with
      | (true, false) -> `Open
      | (false, true) -> `Open
      | (false, false) ->
        (* CR wduff: Better error message. *)
        raise_s [%message "unknown sort" (name : string)]
      | (true, true) ->
        raise_s [%message "Abbot bug: found non-unique name" (name : string)]
    end
  | Bind (lhs, rhs) ->
    let _lhs_constraint = check_abt ~abt_names ~symbol_names ~sort_names lhs in
    let rhs_constraint = check_abt ~abt_names ~symbol_names ~sort_names rhs in
    let required_to_be_closed =
      match rhs_constraint with
      | `Closed { required_to_be_closed } -> required_to_be_closed
      | `Unknown { open_if_any_open } -> open_if_any_open
      | `Simple _ ->
        (* CR wduff: Better error message. *)
        raise_s [%message "Type mismatch"]
      | `Open ->
        (* CR wduff: Better error message. *)
        raise_s [%message "binding to the right of a dot"]
    in
    `Closed { required_to_be_closed }

and check_simple_abt_use ~abt_names ~symbol_names ~sort_names ~name:_ ~arity ~args =
  match Int.equal arity (List.length args) with
  | false ->
    (* CR wduff: Better error message. *)
    raise_s [%message "Arity mismatch" (arity : int) (List.length args : int)]
  | true ->
    List.map args ~f:(check_abt ~abt_names ~symbol_names ~sort_names)
    |> merge_constraints_list
;;

let check_cases ~abt_names ~symbol_names ~sort_names cases =
  List.map cases ~f:(fun (_constructor_name, abt) ->
    match abt with
    | None -> `Unknown { open_if_any_open = String.Set.empty }
    | Some abt -> check_abt ~abt_names ~symbol_names ~sort_names abt)
  |> merge_constraints_list
;;

let check_defn_body ~abt_names ~symbol_names ~sort_names (body : Parse_tree.Defn_body.t) =
  match body with
  | External_abt -> `External_simple_abt
  | Internal_abt cases ->
    begin
      match check_cases ~abt_names ~symbol_names ~sort_names cases with
      | `Simple closed_abt_constraint -> `Simple_abt closed_abt_constraint
      | `Open -> `Open_abt
      | `Closed closed_abt_constraint -> `Closed_abt closed_abt_constraint
      | `Unknown unknown_abt_constraint -> `Unknown_abt unknown_abt_constraint
    end
  | Symbol -> `Symbol
  | Sort cases ->
    begin
      match check_cases ~abt_names ~symbol_names ~sort_names cases with
      | `Closed closed_abt_constraint -> `Sort closed_abt_constraint
      | `Unknown { open_if_any_open } -> `Sort { required_to_be_closed = open_if_any_open }
      | `Simple _ ->
        (* CR wduff: Better error message. *)
        raise_s [%message "Sorts may not have arguments"]
      | `Open ->
        (* CR wduff: Better error message. *)
        raise_s [%message "unclosed binding in sort"]
    end
;;

module Abt_list = struct
  type 'a t = 'a Typed.Abt.t list
end

module Abt_option = struct
  type 'a t = 'a Typed.Abt.t option
end

let rec translate_abt ~defn_types (abt : Parse_tree.Abt.t)
  : Typed.Packed_with_kind_or_poly (Typed.Abt).t =
  match abt with
  | Use (name, args) ->
    begin
      match args with
      | [] ->
        begin
          match Map.find_exn defn_types name with
          | `Builtin_abt builtin_abt -> T (Poly, Builtin_abt_use (builtin_abt, []))
          | `Simple_abt -> T (Poly, Simple_abt_use (name, []))
          | `Open_abt -> T (Open, Open_abt_use name)
          | `Closed_abt -> T (Poly, Closed_abt_use name)
          | `Symbol -> T (Poly, Symbol_use name)
          | `Sort -> T (Poly, Sort_use name)
        end
      | _ :: _ ->
        begin
          let (T (kind, args) : Typed.Packed_with_kind_or_poly (Abt_list).t) =
            translate_abts ~defn_types args
          in
          match Map.find_exn defn_types name with
          | `Builtin_abt builtin_abt ->
            T (kind, Builtin_abt_use (builtin_abt, args))
          | `Simple_abt ->
            T (kind, Simple_abt_use (name, args))
          | `Open_abt | `Closed_abt | `Symbol | `Sort ->
            (* CR wduff: Better error. *)
            raise_s [%message "Only simple abts support parameterization at this time."]
        end
    end
  | Arg_use name ->
    T (Simple, Arg_use name)
  | Prod abts ->
    let (T (kind, abts)) = translate_abts ~defn_types abts in
    T (kind, Prod abts)
  | Binding name ->
    begin
      match Map.find_exn defn_types name with
      | `Builtin_abt _ | `Simple_abt | `Open_abt | `Closed_abt ->
        (* CR wduff: Better error. *)
        raise_s [%message "Only sorts and symbols can be bound."]
      | `Symbol ->
        T (Open, Symbol_binding name)
      | `Sort ->
        T (Open, Sort_binding name)
    end
  | Bind (lhs, rhs) ->
    let (T (lhs_kind, lhs)) = translate_abt ~defn_types lhs in
    let (T (rhs_kind, rhs)) = translate_abt ~defn_types rhs in
    let (lhs : [ `Open ] Typed.Abt.t) =
      match lhs_kind with
      | Poly -> Typed.Abt.cast_poly lhs
      | Open -> lhs
      | Simple ->
        (* CR wduff: Better error message. *)
        raise_s [%message ""]
      | Closed ->
        (* CR wduff: Better error message. *)
        raise_s [%message ""]
    in
    let (rhs : [ `Closed ] Typed.Abt.t)  =
      match rhs_kind with
      | Poly -> Typed.Abt.cast_poly rhs
      | Closed -> rhs
      | Simple ->
        (* CR wduff: Better error message. *)
        raise_s [%message ""]
      | Open ->
        (* CR wduff: Better error message. *)
        raise_s [%message ""]
    in
    T (Closed, Bind (lhs, rhs))

and translate_abts ~defn_types abts =
  List.fold_right abts ~init:(T (Poly, []))
    ~f:(fun abt (T (kind, abts) : Typed.Packed_with_kind_or_poly (Abt_list).t) ->
    let (T (kind', abt)) = translate_abt ~defn_types abt in
    match (kind, kind') with
    | (Poly, Poly) -> T (Poly, abt :: abts)
    | (Poly, Simple) -> T (Simple, abt :: (List.map abts ~f:Typed.Abt.cast_poly))
    | (Simple, Poly) -> T (Simple, Typed.Abt.cast_poly abt :: abts)
    | (Simple, Simple) -> T (Simple, abt :: abts)
    | (Poly, Open) -> T (Open, abt :: (List.map abts ~f:Typed.Abt.cast_poly))
    | (Open, Poly) -> T (Open, Typed.Abt.cast_poly abt :: abts)
    | (Open, Open) -> T (Open, abt :: abts)
    | (Closed, Closed) -> T (Closed, abt :: abts)
    | (Poly, Closed) -> T (Closed, abt :: (List.map abts ~f:Typed.Abt.cast_poly))
    | (Closed, Poly) -> T (Closed, Typed.Abt.cast_poly abt :: abts)
    | (Simple, Open) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""]
    | (Open, Simple) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""]
    | (Simple, Closed) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""]
    | (Closed, Simple) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""]
    | (Open, Closed) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""]
    | (Closed, Open) ->
      (* CR wduff: Better error? This should be impossible. *)
      raise_s [%message ""])
;;

let translate_cases ~defn_types cases =
  List.fold_right cases ~init:(T (Poly, []))
    ~f:(fun (constructor_name, abt) (T (kind, cases) : Typed.Packed_with_kind_or_poly (Typed.Cases).t) ->
      let (T (kind', abt) : Typed.Packed_with_kind_or_poly (Abt_option).t) =
        match abt with
        | None ->
          (T (Poly, None) : Typed.Packed_with_kind_or_poly (Abt_option).t)
        | Some abt ->
          let (T (kind, abt)) = translate_abt ~defn_types abt in
          T (kind, Some abt)
      in
      match (kind, kind') with
      | (Poly, Poly) ->
        T (Poly, (constructor_name, abt) :: cases)
      | (Poly, Simple) ->
        T (Simple, (constructor_name, abt) :: Typed.Cases.cast_poly cases)
      | (Simple, Poly) ->
        T (Simple, (constructor_name, Option.map abt ~f:Typed.Abt.cast_poly) :: cases)
      | (Simple, Simple) ->
        T (Simple, (constructor_name, abt) :: cases)
      | (Poly, Open) ->
        T (Open, (constructor_name, abt) :: Typed.Cases.cast_poly cases)
      | (Open, Poly) ->
        T (Open, (constructor_name, Option.map abt ~f:Typed.Abt.cast_poly) :: cases)
      | (Open, Open) ->
        T (Open, (constructor_name, abt) :: cases)
      | (Closed, Closed) ->
        T (Closed, (constructor_name, abt) :: cases)
      | (Poly, Closed) ->
        T (Closed, (constructor_name, abt) :: Typed.Cases.cast_poly cases)
      | (Closed, Poly) ->
        T (Closed, (constructor_name, Option.map abt ~f:Typed.Abt.cast_poly) :: cases)
      | (Simple, Open) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""]
      | (Open, Simple) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""]
      | (Simple, Closed) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""]
      | (Closed, Simple) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""]
      | (Open, Closed) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""]
      | (Closed, Open) ->
        (* CR wduff: Better error? This should be impossible. *)
        raise_s [%message ""])
;;

let translate_defn_body ~defn_types (body : Parse_tree.Defn_body.t) : Typed.Defn_body.t =
  match body with
  | External_abt -> External_simple_abt
  | Internal_abt cases ->
    let (cases : Typed.Cases.Packed.t) =
      match translate_cases ~defn_types cases with
      | T (Poly, cases) -> T (Simple, Typed.Cases.cast_poly cases)
      | T (Simple, cases) -> T (Simple, cases)
      | T (Open, cases) -> T (Open, cases)
      | T (Closed, cases) -> T (Closed, cases)
    in
    Internal_abt cases
  | Symbol -> Symbol
  | Sort cases ->
    begin
      match translate_cases ~defn_types cases with
      | T (Closed, cases) -> Sort cases
      | T (Poly, cases) -> Sort (Typed.Cases.cast_poly cases)
      | T (Simple, _) ->
        (* CR wduff: Better error message. *)
        raise_s [%message ""]
      | T (Open, _) ->
        (* CR wduff: Better error message. *)
        raise_s [%message "unclosed binding in sort"]
    end
;;

(* CR wduff: Check that things with arguments are simple. *)
let check_defns (defns : Parse_tree.Defn.t list) =
  let all_names = String.Hash_set.create () in
  let (abt_names, symbol_names, sort_names) =
    List.fold defns
      ~init:(String.Map.empty, String.Set.empty, String.Set.empty)
      ~f:(fun (abt_names, symbol_names, sort_names) { name; args; body } ->
          begin
            match Hash_set.strict_add all_names name with
            | Ok () -> ()
            | Error _ ->
              (* CR wduff: Better error message. *)
              raise_s [%message "Duplicate name" (name : string)]
          end;
          match body with
          | External_abt | Internal_abt _ ->
            (Map.add_exn abt_names ~key:name ~data:(List.length args), symbol_names, sort_names)
          | Symbol ->
            begin
              match List.length args with
              | 0 -> (abt_names, Set.add symbol_names name, sort_names)
              | _ ->
                (* CR wduff: Better error message. *)
                raise_s [%message "Symbols cannot be parameterized"]
            end
          | Sort _ ->
            begin
              match List.length args with
              | 0 -> (abt_names, symbol_names, Set.add sort_names name)
              | _ ->
                (* CR wduff: Better error message. *)
                raise_s [%message "Symbols cannot be parameterized"]
            end)
  in
  let defn_types =
    List.map Builtin_abt.all ~f:(fun builtin_abt ->
      (Builtin_abt.name builtin_abt, `Builtin_abt builtin_abt))
    @
    List.map defns ~f:(fun { name; args = _; body } ->
      (name, check_defn_body ~abt_names ~symbol_names ~sort_names body))
  in
  let open_abt_names =
    List.filter_map defn_types ~f:(fun (name, body_type) ->
        match body_type with
        | `Open_abt -> Some name
        | _ -> None)
    |> String.Hash_set.of_list
  in
  (* CR-someday wduff: This could be optimized, but it probably doesn't matter. *)
  let rec propagate_openness defn_types =
    let (something_changed, defn_types) =
      List.fold_map defn_types ~init:false
        ~f:(fun acc (name, body_type) ->
            match body_type with
            | `Unknown_abt { open_if_any_open }
              when List.exists (Set.to_list open_if_any_open) ~f:(Hash_set.mem open_abt_names) ->
              (true, (name, `Open_abt))
            | _ ->
              (acc, (name, body_type)))
    in
    match something_changed with
    | true -> propagate_openness defn_types
    | false -> defn_types
  in
  let (defn_types, required_to_be_closed) =
    propagate_openness defn_types
    |> List.map ~f:(fun (name, body_type) ->
        match body_type with
        | `Builtin_abt builtin_abt ->
          ((name, `Builtin_abt builtin_abt), String.Set.empty)
        | `External_simple_abt ->
          ((name, `Simple_abt), String.Set.empty)
        | `Simple_abt { required_to_be_closed } ->
          ((name, `Simple_abt), required_to_be_closed)
        | `Open_abt ->
          ((name, `Open_abt), String.Set.empty)
        | `Closed_abt { required_to_be_closed } ->
          ((name, `Closed_abt), required_to_be_closed)
        | `Unknown_abt { open_if_any_open = _ } ->
          (* At this point we know that none of the dependencies
             are open, so we know this is simple. *)
          ((name, `Simple_abt), String.Set.empty)
        | `Symbol ->
          ((name, `Symbol), String.Set.empty)
        | `Sort { required_to_be_closed } ->
          ((name, `Sort), required_to_be_closed))
    |> List.unzip
  in
  String.Set.union_list required_to_be_closed
  |> Set.iter ~f:(fun abt_name ->
    match Hash_set.mem open_abt_names abt_name with
    | false -> ()
    | true ->
      (* CR wduff: Better error message. *)
      raise_s [%message "open abt appears to the right of a dot"]);
  let defn_types = String.Map.of_alist_exn defn_types in
  let translated_defns =
    List.map defns ~f:(fun { name; args; body } : Typed.Defn.t ->
      { name; args; body = translate_defn_body ~defn_types body })
  in
  translated_defns
;;
