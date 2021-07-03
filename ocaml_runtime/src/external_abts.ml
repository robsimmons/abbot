open! Core
include External_abts_intf

module Make0 (T : sig type t [@@deriving sexp_of] end) = struct
  type t = T.t [@@deriving sexp_of]

  let fold_map acc t = (acc, t)

  let apply_subst _ t = t
end

module Make1
    (T : sig
       type 'a t [@@deriving sexp_of]

       val map : 'a t -> f:('a -> 'b) -> 'b t
       val fold_map : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t
     end)
=
struct
  type 'a t = 'a T.t [@@deriving sexp_of]

  let fold_map f init t = T.fold_map t ~init ~f

  (* We need to define this explicitly, instead of just doing this at the call sites because the
     call sites don't distinguish between internal and external abts, and for internal abts there
     may be other work to do, because they can directly contain things we need to substitute into.
  *)
  let apply_subst apply_subst_a subst t =
    T.map t ~f:(apply_subst_a subst)
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

    let map = Option.map

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

    let map = List.map

    let fold_map = List.fold_map
  end)

module String_map =
  Make1 (struct
    type 'a t = 'a Core.String.Map.t [@@deriving sexp_of]

    let map = Core.String.Map.map

    let fold_map t ~init ~f =
      Core.String.Map.fold t ~init:(init, Core.String.Map.empty) ~f:(fun ~key ~data (acc, new_map) ->
        let (acc, data) = f acc data in
        (acc, Core.String.Map.add_exn new_map ~key ~data))
  end)
