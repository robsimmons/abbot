open! Core

(* CR wduff: Rename "use" to "reference"? *)
module Abt : sig
  type t =
    | Use of string * t list
    | Arg_use of string
    | Prod of t list
    | Binding of string
    | Bind of t * t
end

module Cases : sig
  type t = (string * Abt.t option) list
end

module Defn_body : sig
  type t =
    | External_abt
    | Internal_abt of Cases.t
    | Symbol
    | Sort of Cases.t
end

module Defn : sig
  type t =
    { name : string; args : string list; body : Defn_body.t }
end
