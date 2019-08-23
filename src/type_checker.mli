open! Core

(* CR wduff: Rename to kind checker. *)
val check_defns : Parse_tree.Defn.t list -> Typed.Defn.t list
