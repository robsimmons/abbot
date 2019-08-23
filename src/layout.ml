open! Core

module Indentation = struct
  type t =
    | Indent
    | No_indent
end

type t =
  | Atom of string
  | Atom_magnet_left of string
  | Atom_magnet_right of string
  | Atom_magnet_both of string
  | List of (Indentation.t * t) list

module Spaces = struct
  type t =
    | Both_spaces
    | Left_space
    | Right_space
    | No_spaces
end

module With_lengths = struct
  type t =
    { length : int; tree : tree }

  and tree =
    | Atom of string
    | List of [ `Layout of Indentation.t * t | `Space ] list
  [@@deriving fields]

  let rec to_flat_string { length = _; tree } =
    tree_to_flat_string tree

  and tree_to_flat_string tree =
    match tree with
    | Atom string -> string
    | List sub_parts ->
      List.map sub_parts ~f:(function
        | `Space -> " "
        | `Layout ((_ : Indentation.t), sub_part) -> to_flat_string sub_part)
      |> String.concat
  ;;

  let rec to_lines { length; tree } ~max_length ~indent_amount =
    match length <= max_length with
    | true -> [ tree_to_flat_string tree ]
    | false ->
      tree_to_lines tree ~max_length ~indent_amount

  and tree_to_lines tree ~max_length ~indent_amount =
      match tree with
      | Atom string -> [ String.init indent_amount ~f:(const ' ') ^ string ]
      | List sub_parts ->
        List.concat_map sub_parts ~f:(function
          | `Space -> []
          | `Layout (indentation, sub_part) ->
            match indentation with
            | Indent ->
              to_lines ~max_length:(max_length - 2) ~indent_amount:(indent_amount + 2) sub_part
              |> List.map  ~f:(fun line -> "  " ^ line)
            | No_indent ->
              to_lines ~max_length ~indent_amount sub_part)
  ;;

  let to_string t ~max_length =
    String.concat ~sep:"\n" (to_lines t ~max_length ~indent_amount:0) ^ "\n"
  ;;
end

let rec add_lengths (t : t) : Spaces.t * With_lengths.t =
  match t with
  | Atom string ->
    (Both_spaces, { length = String.length string; tree = Atom string })
  | Atom_magnet_left string ->
    (Right_space, { length = String.length string; tree = Atom string })
  | Atom_magnet_right string ->
    (Left_space, { length = String.length string; tree = Atom string })
  | Atom_magnet_both string ->
    (No_spaces, { length = String.length string; tree = Atom string })
  | List sub_parts ->
    let ((length, _), sub_parts) =
      (* Length of the sub-parts *)
      List.fold_map sub_parts ~init:(0, true)
        ~f:(fun (acc_length, drop_left_space) (indentation, sub_part) ->
          let (spaces, sub_part) = add_lengths sub_part in
          let (drop_left_space, drop_right_space) =
            match spaces with
            | Both_spaces -> (drop_left_space, false)
            | Left_space -> (drop_left_space, true)
            | Right_space -> (true, false)
            | No_spaces -> (true, true)
          in
          match drop_left_space with
          | true ->
            ((acc_length + With_lengths.length sub_part,
              drop_right_space),
             [ `Layout (indentation, sub_part) ])
          | false ->
            ((acc_length + 1 + With_lengths.length sub_part,
              drop_right_space),
             [ `Space; `Layout (indentation, sub_part) ]))
    in
    (* CR wduff: Is this right? Maybe we should use the spacing rules of the left and rightmost
       sub-element? *)
    (Both_spaces,
     { length; tree = List (List.concat sub_parts) })
;;

let to_string t ~max_length =
  let ((_ : Spaces.t), with_lengths) = add_lengths t in
  With_lengths.to_string with_lengths ~max_length
;;
