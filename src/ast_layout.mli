open! Core
open Ppxlib

val layout_signature : [ `Ocaml | `Sml ] -> signature -> Layout.t

val layout_structure : [ `Ocaml | `Sml ] -> structure -> Layout.t
