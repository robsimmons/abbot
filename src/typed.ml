open! Core

module Kind = struct
  type _ t =
    | Simple : [ `Simple ] t
    | Open : [ `Open ] t
    | Closed : [ `Closed ] t

  module Or_poly = struct
    type _ t =
      | Poly : [ `Poly ] t
      | Simple : [ `Simple ] t
      | Open : [ `Open ] t
      | Closed : [ `Closed ] t
  end
end

module Packed_with_kind (X : T1) = struct
  type t = T : 'k Kind.t * 'k X.t -> t
end

module Packed_with_kind_or_poly (X : T1) = struct
  type t = T : 'k Kind.Or_poly.t * 'k X.t -> t
end

module Abt = struct
  type _ t =
    | Arg_use : string -> [ `Simple ] t
    | Builtin_abt_use : Builtin_abt.t * 'a t list -> 'a t
    | Simple_abt_use : string * 'a t list -> 'a t
    | Open_abt_use : string -> [ `Open ] t
    | Closed_abt_use : string -> _ t
    | Symbol_use : string -> _ t
    | Sort_use : string -> _ t
    | Prod : 'a t list -> 'a t
    | Symbol_binding : string -> [ `Open ] t
    | Sort_binding : string -> [ `Open ] t
    | Bind : [ `Open ] t * [ `Closed ] t -> [ `Closed ] t

  module Untyped = struct
    type t =
      | Arg_use of string
      | Builtin_abt_use of Builtin_abt.t * t list
      | Simple_abt_use of string * t list
      | Open_abt_use of string
      | Closed_abt_use of string
      | Symbol_use of string
      | Sort_use of string
      | Prod of t list
      | Symbol_binding of string
      | Sort_binding of string
      | Bind of t * t
    [@@deriving compare, sexp]
  end

  let rec to_untyped : type a. a t -> Untyped.t = function
    | Arg_use name -> Arg_use name
    | Builtin_abt_use (builtin_abt, args) ->
      Builtin_abt_use (builtin_abt, List.map args ~f:to_untyped)
    | Simple_abt_use (name, args) -> Simple_abt_use (name, List.map args ~f:to_untyped)
    | Open_abt_use name -> Open_abt_use name
    | Closed_abt_use name -> Closed_abt_use name
    | Symbol_use name -> Symbol_use name
    | Sort_use name -> Sort_use name
    | Prod ts -> Prod (List.map ts ~f:to_untyped)
    | Symbol_binding name -> Symbol_binding name
    | Sort_binding name -> Sort_binding name
    | Bind (lhs, rhs) -> Bind (to_untyped lhs, to_untyped rhs)
  ;;

  let sexp_of_t t = [%sexp_of: Untyped.t] (to_untyped t)
  let compare t1 t2 = Untyped.compare (to_untyped t1) (to_untyped t2)

  let rec cast_poly (t : [ `Poly ] t) : 'a t =
    match t with
    | Builtin_abt_use (builtin_abt, args) ->
      Builtin_abt_use (builtin_abt, List.map args ~f:cast_poly)
    | Simple_abt_use (name, args) -> Simple_abt_use (name, List.map args ~f:cast_poly)
    | Closed_abt_use name -> Closed_abt_use name
    | Symbol_use name -> Symbol_use name
    | Sort_use name -> Sort_use name
    | Prod ts -> Prod (List.map ts ~f:cast_poly)
  ;;
end

module Cases = struct
  module T = struct
    type 'a t = (string * 'a Abt.t option) list

    let cast_poly t =
      List.map t ~f:(fun (constructor_name, abt_opt) ->
        (constructor_name, Option.map abt_opt ~f:Abt.cast_poly))
    ;;
  end

  include T
  module Packed = Packed_with_kind (T)
end

module Defn_body = struct
  type t =
    | External_simple_abt
    | Internal_abt of Cases.Packed.t
    | Symbol
    | Sort of [ `Closed ] Cases.t
end

module Defn = struct
  type t =
    { name : string; args : string list; body : Defn_body.t }
  [@@deriving fields]
end
