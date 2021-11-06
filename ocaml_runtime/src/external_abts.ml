open! Base
include External_abts_intf

module Make1
    (T : sig
       type 'a t [@@deriving sexp_of]

       val map : 'a t -> f:('a -> 'b) -> 'b t
       val fold_map : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc * 'b) -> 'acc * 'b t
     end)
=
struct
  type 'a t = 'a T.t [@@deriving sexp_of]

  let map f t = T.map t ~f
  let fold_map f init t = T.fold_map t ~init ~f
end

module Unit = struct
  type t = unit [@@deriving sexp_of]
end

module Int = struct
  type t = int [@@deriving sexp_of]
end

module Int64 = struct
  type t = Int64.t [@@deriving sexp_of]
end

module Char = struct
  type t = char [@@deriving sexp_of]
end

module String = struct
  type t = string [@@deriving sexp_of]
end

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
