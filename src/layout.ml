open! Core

module Indentation = struct
  type t =
    | Indent
    | No_indent
end

module rec Self : sig
  module Dynamic : sig
    module List_elt : sig
      type t =
        | Space
        | Non_space of Indentation.t * Self.Dynamic.t
    end

    module Tree : sig
      type t =
        | Atom of string
        | List of List_elt.t list
        | If_fits_on_line of { then_ : Self.Dynamic.t; else_ : Self.t }
    end

    module Poly : sig
      type 'a t =
        { tree : 'a
        ; length_on_single_line : int
        ; magnet_left : bool
        ; magnet_right : bool
        }
    end

    type t = Tree.t Poly.t
  end

  module Multi_line : sig
    type t =
      | Always_split_list of (Indentation.t * Self.t) list
  end

  type t =
    | Dynamic of Dynamic.t
    | Multi_line of Multi_line.t
end = Self

include Self

let to_dynamic : t -> Dynamic.t option = function
  | Dynamic t -> Some t
  | Multi_line _ -> None
;;

let map_dynamic_poly (t : _ Dynamic.Poly.t) ~f : _ Dynamic.Poly.t =
  { t with tree = f t.tree }
;;

let atom ?(magnet_left = false) ?(magnet_right = false) string : t =
  Dynamic
    { tree = Atom string
    ; length_on_single_line = String.length string
    ; magnet_left
    ; magnet_right
    }
;;

let always_split_list (sub_parts : (Indentation.t * t) list) : t =
  match sub_parts with
  | [] ->
    raise_s [%message "Layout.always_split_list got empty list"]
  | _ :: _ ->
    Multi_line (Always_split_list sub_parts)
;;

let list (sub_parts : (Indentation.t * t) list) : t =
  match sub_parts with
  | [] ->
    raise_s [%message "Layout.list got empty list"]
  | _ :: _ ->
    match
      List.map sub_parts ~f:(fun (indentation, sub_part) ->
        Option.map (to_dynamic sub_part) ~f:(fun sub_part -> (indentation, sub_part)))
      |> Option.all
    with
    | None -> always_split_list sub_parts
    | Some sub_parts ->
      let sub_parts =
        List.map sub_parts ~f:(fun (indentation, sub_part) ->
          { sub_part with
            tree = [ Dynamic.List_elt.Non_space (indentation, sub_part) ]
          })
      in
      List.reduce_balanced_exn sub_parts ~f:(fun left right ->
        let (space_length, maybe_space) =
          match left.magnet_right || right.magnet_left with
          | true -> (0, [])
          | false -> (1, [ Dynamic.List_elt.Space ])
        in
        { tree = left.tree @ maybe_space @ right.tree
        ; length_on_single_line =
            left.length_on_single_line + space_length + right.length_on_single_line
        ; magnet_left = left.magnet_left
        ; magnet_right = right.magnet_right
        })
      |> map_dynamic_poly ~f:(fun sub_parts -> Dynamic.Tree.List sub_parts)
      |> Dynamic
;;

let if_fits_on_line ~then_ ~else_ =
  match to_dynamic then_ with
  | None -> else_
  | Some then_ ->
    Dynamic
      { then_ with
        tree = If_fits_on_line { then_; else_ }
      }
;;

let rec dynamic_to_flat_string ({ tree; _ } : Dynamic.t) =
  dynamic_tree_to_flat_string tree

and dynamic_tree_to_flat_string tree =
  match tree with
  | Atom string -> string
  | List sub_parts ->
    List.map sub_parts ~f:(function
      | Space -> " "
      | Non_space ((_ : Indentation.t), sub_part) -> dynamic_to_flat_string sub_part)
    |> String.concat
  | If_fits_on_line { then_; else_ = _ } ->
    dynamic_to_flat_string then_
;;

let list_to_lines
      ~to_lines
      (list : (Indentation.t * 'a) list)
      ~spaces_to_indent
      ~max_line_length
      ~outer_indentation
  =
  List.concat_map list ~f:(fun (indentation, sub_part) ->
    match indentation with
    | Indent ->
      to_lines
        sub_part
        ~spaces_to_indent
        ~max_line_length:(max_line_length - spaces_to_indent)
        ~outer_indentation:(outer_indentation + spaces_to_indent)
      |> List.map  ~f:(fun line -> "  " ^ line)
    | No_indent ->
      to_lines sub_part ~spaces_to_indent ~max_line_length ~outer_indentation)
;;

let rec to_lines (t : t) =
  match t with
  | Dynamic t -> dynamic_to_lines t
  | Multi_line t -> multi_line_to_lines t

and dynamic_to_lines
          ({ tree; length_on_single_line; magnet_left = _; magnet_right = _ } : Dynamic.t)
          ~spaces_to_indent
          ~max_line_length
          ~outer_indentation
  : string list =
  match length_on_single_line <= max_line_length with
  | true -> [ dynamic_tree_to_flat_string tree ]
  | false ->
    dynamic_tree_to_lines tree ~max_line_length ~spaces_to_indent ~outer_indentation

and dynamic_tree_to_lines tree ~spaces_to_indent ~max_line_length ~outer_indentation =
  match tree with
  | Atom string -> [ String.init outer_indentation ~f:(const ' ') ^ string ]
  | List sub_parts ->
    List.filter_map sub_parts ~f:(function
      | Space -> None
      | Non_space (indentation, sub_part) -> Some (indentation, sub_part))
    |> list_to_lines
         ~to_lines:dynamic_to_lines
         ~spaces_to_indent
         ~max_line_length
         ~outer_indentation
  | If_fits_on_line { then_ = _; else_ } ->
    to_lines else_ ~spaces_to_indent ~max_line_length ~outer_indentation

and multi_line_to_lines t ~spaces_to_indent ~max_line_length ~outer_indentation =
  match t with
  | Always_split_list sub_parts ->
    list_to_lines
      sub_parts
      ~to_lines
      ~spaces_to_indent
      ~max_line_length
      ~outer_indentation
;;

let to_string ?(spaces_to_indent = 2) t ~max_line_length =
  String.concat
    ~sep:"\n"
    (to_lines t ~spaces_to_indent ~max_line_length ~outer_indentation:0)
  ^ "\n"
;;
