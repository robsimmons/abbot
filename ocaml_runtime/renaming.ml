open! Core

type t = Internal_var.t -> Internal_var.t

let apply t = t

let ident var = var

let compose t1 t2 var = t1 (t2 var)

let bind free_var : t = function
  | Bound_var bound_var -> Bound_var bound_var
  | Free_var free_var' ->
    match Temp.equal free_var free_var' with
    | false -> Free_var free_var'
    | true -> Bound_var 0
;;

let shift : t = function
  | Free_var free_var -> Free_var free_var
  | Bound_var bound_var -> Bound_var (bound_var + 1)
;;

let bind' free_vars =
  List.fold free_vars ~init:ident ~f:(fun acc free_var ->
    compose (bind free_var) (compose shift acc))
;;

let unbind (t : t) free_var : t = function
  | Free_var free_var' -> shift (t (Free_var free_var'))
  | Bound_var bound_var ->
    match bound_var with
    | 0 -> Free_var free_var
    | _ -> shift (t (Bound_var (bound_var - 1)))
;;

let unbind' t free_vars =
  List.fold free_vars ~init:t ~f:unbind
;;
