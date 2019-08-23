open! Core

(* CR wduff: Should we handle product as if it were an infix built-in? *)
type t =
  | Unit
  | Int
  | Int64
  | Char
  | String
  | Option
  | List
  | String_map
[@@deriving compare, enumerate, sexp]

let of_name = function
  | "unit" -> Some Unit
  | "int" -> Some Int
  | "int64" -> Some Int64
  | "char" -> Some Char
  | "string" -> Some String
  | "option" -> Some Option
  | "list" -> Some List
  | "string_map" -> Some String_map
  | _ -> None
;;

let name = function
  | Unit -> "unit"
  | Int -> "int"
  | Int64 -> "int64"
  | Char -> "char"
  | String -> "string"
  | Option -> "option"
  | List -> "list"
  | String_map -> "string_map"
;;

let%expect_test _ =
  List.iter all ~f:(fun t ->
    assert ([%compare.equal: t option] (Some t) (of_name (name t))));
  [%expect {| |}]
;;

let arity = function
  | Unit | Int | Int64 | Char | String -> 0
  | Option | List | String_map -> 1
;;

let core_type = function
  | Unit -> "unit"
  | Int -> "int"
  | Int64 -> "Int64.t"
  | Char -> "char"
  | String -> "string"
  | Option -> "option"
  | List -> "list"
  | String_map -> "String.Map.t"
;;

let module_name t = sprintf "External_abts.%s" (String.capitalize (name t))
