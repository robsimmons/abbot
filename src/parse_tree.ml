open! Core

module Abt = struct
  type t =
    | Use of string * t list
    | Arg_use of string
    | Prod of t list
    | Binding of string
    | Bind of t * t
end

module Cases = struct
  type t = (string * Abt.t option) list
end

module Defn_body = struct
  type t =
    | External_abt
    | Internal_abt of Cases.t
    | Symbol
    | Sort of Cases.t
end

module Defn = struct
  type t =
    { name : string; args : string list; body : Defn_body.t }
end
