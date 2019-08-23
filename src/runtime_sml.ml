(* CR wduff: Consider deleting this and instead providing a runtime library. *)

open! Core
open Ppxlib

let loc = Location.none

let temp_intf =
  Ast_helper.Mtd.mk { txt = "TEMP"; loc }
    ~typ:
      (Ast_helper.Mty.signature
         [%sig:
           type t

           (* Creates a new, globally unique temp. *)
           val create : string -> t

           (* Provides the string used to create the temp. *)
           val name : t -> string

           val eq : t * t -> bool
           val compare : t * t -> order
           val hash : t -> word
         ])
;;

let structure =
  [%str
module Temp : TEMP = struct
  type t = string * int

  let counter = ref 0

  let create s = (s, (counter := !counter + 1; !counter))

  let hash (_, id) = Word.fromInt id

  let eq ((_, (id1 : int)), (_, (id2 : int))) = id1 = id2

  let compare ((_, id1), (_, id2)) = Int.compare (id1, id2)

  let name (s, _) = s
end

type 'a compare_ignore = 'a

let failwith string = raise (Fail string)

module Internal_var = struct
  type t =
    | Free_var of Temp.t
    | Bound_var of int
end

module Renaming = struct
  type t = Internal_var.t -> Internal_var.t

  let apply t = t

  let ident var = var

  let compose t1 t2 var = t1 (t2 var)

  let bind (free_var : Temp.t) (var : Internal_var.t) : Internal_var.t =
    match var with
    | Internal_var.Bound_var bound_var -> Internal_var.Bound_var bound_var
    | Internal_var.Free_var free_var' ->
      match Temp.eq (free_var, free_var') with
      | false -> Internal_var.Free_var free_var'
      | true -> Internal_var.Bound_var 0
  ;;

  let shift (var : Internal_var.t) : Internal_var.t =
    match var with
    | Internal_var.Free_var free_var -> Internal_var.Free_var free_var
    | Internal_var.Bound_var bound_var -> Internal_var.Bound_var (bound_var + 1)
  ;;

  let bind' free_vars =
    List.foldl
      (fun (free_var, acc) ->
         compose (bind free_var) (compose shift acc))
      ident
      free_vars
  ;;

  let unbind (t : t) (free_var : Temp.t) (var : Internal_var.t) : Internal_var.t =
    match var with
    | Internal_var.Free_var free_var' -> shift (t (Internal_var.Free_var free_var'))
    | Internal_var.Bound_var bound_var ->
      match bound_var with
      | 0 -> Internal_var.Free_var free_var
      | _ -> shift (t (Internal_var.Bound_var (bound_var - 1)))
  ;;

  let unbind' t free_vars =
    List.foldl (fun (free_var, acc) -> unbind acc free_var) t free_vars
  ;;
end

module With_renaming = struct
  type 'oper t = Renaming.t * 'oper

  let apply_renaming renaming (renaming', oper) = (Renaming.compose renaming renaming', oper)
end

module Internal_sort = struct
  type 'oper t =
    | Var of Internal_var.t
    | Oper of 'oper With_renaming.t

  let apply_renaming renaming (t : 'oper t) =
    match t with
    | Var var -> Var (Renaming.apply renaming var)
    | Oper (renaming', oper) -> Oper (Renaming.compose renaming renaming', oper)
end
]
;;
