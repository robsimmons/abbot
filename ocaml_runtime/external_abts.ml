open! Core

module type S0 = sig
  type t [@@deriving sexp_of]

  val apply_renaming : Renaming.t -> 'acc -> t -> 'acc * t
  val subst : 'sort -> 'value -> 'var -> t -> t
end

module type S1 = sig
  type 'a t [@@deriving sexp_of]

  val apply_renaming
    : (Renaming.t -> 'acc -> 'a1 -> 'acc * 'a2) -> Renaming.t -> 'acc -> 'a1 t -> 'acc * 'a2 t

  val subst : ('sort -> 'value -> 'var -> 'a -> 'a) -> 'sort -> 'value -> 'var -> 'a t -> 'a t
end

(* CR wduff: Consider exposing these functors and call them in the generated code for non-builtin
   external abts, for the arities we support. *)
module Make0 (T : sig type t [@@deriving sexp_of] end) = struct
  type t = T.t [@@deriving sexp_of]

  let apply_renaming _ acc t = (acc, t)
  let subst _ _ _ t = t
end

module Make1
    (T : sig
       type 'a t [@@deriving sexp_of]

       val fold_map
         :  'a t
         -> init:'acc
         -> f:('acc -> 'a -> 'acc * 'b)
         -> 'acc * 'b t
     end)
=
struct
  type 'a t = 'a T.t [@@deriving sexp_of]

  let apply_renaming apply_renaming_a renaming acc t =
    T.fold_map t ~init:acc ~f:(apply_renaming_a renaming)

  let subst subst_a sort value var t =
    let ((), t) =
      T.fold_map
        t
        ~init:()
        ~f:(fun () -> (fun a -> ((), subst_a sort value var a)))
    in
    t
end

module Unit =
  Make0 (struct
    type t = unit [@@deriving sexp_of]
  end)

module Int =
  Make0 (struct
    type t = int [@@deriving sexp_of]
  end)

module Int64 =
  Make0 (struct
    type t = Int64.t [@@deriving sexp_of]
  end)

module Char =
  Make0 (struct
    type t = char [@@deriving sexp_of]
  end)

module String =
  Make0 (struct
    type t = string [@@deriving sexp_of]
  end)

module Option =
  Make1 (struct
    type 'a t = 'a option [@@deriving sexp_of]

    let fold_map t ~init ~f =
      match t with
      | None -> (init, None)
      | Some data ->
        let (acc, data) = f init data in
        (acc, Some data)
  end)

module List =
  Make1 (struct
    type 'a t = 'a list [@@deriving sexp_of]

    let fold_map = List.fold_map
  end)

module String_map =
  Make1 (struct
    type 'a t = 'a Core.String.Map.t [@@deriving sexp_of]

    let fold_map t ~init ~f =
      Core.String.Map.fold t ~init:(init, Core.String.Map.empty) ~f:(fun ~key ~data (acc, new_map) ->
        let (acc, data) = f acc data in
        (acc, Core.String.Map.add_exn new_map ~key ~data))
  end)
