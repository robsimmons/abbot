open! Core

(* CR wduff: It's tempting to have something like a map here, but it's tricky because order
   matters. *)
type t = Internal_var.t -> Internal_var.t

let apply t = t

let ident var = var

let compose t1 t2 var = t1 (t2 var)

(* CR wduff: Does bind need to shift bound vars up out of the way? Maybe bind just can't encounter
   bounds vars unless it is already shifted somehow? *)
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

(* CR wduff: It's not clear to me that bind' and unbind' don't flip the ordering. Shouldn't they run
   in opposite orders so the thing that you bind last, which gets the least shifting, is the thing
   you unbind first? *)

(* CR wduff: Test that this is equivalent to a map/table lookup that returns [Bound_var n] for the
   nth free var, then replace it with that more efficient implementation. Maybe this can be subsumed
   by some more general change of [t] from a function to something faster. *)
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
