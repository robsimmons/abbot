structure Renaming :> RENAMING = struct
type t = Internal_var.t -> Internal_var.t

fun apply t = t

fun ident var = var

fun compose t1 t2 var = t1 (t2 var)

fun bind free_var (Internal_var.Bound_var bound_var) = Internal_var.Bound_var bound_var
  | bind free_var (Internal_var.Free_var free_var') =
    case Temp.eq (free_var, free_var')
     of false => Internal_var.Free_var free_var'
      | true => Internal_var.Bound_var 0

fun shift (Internal_var.Free_var free_var) = Internal_var.Free_var free_var
  | shift (Internal_var.Bound_var bound_var) = Internal_var.Bound_var (bound_var + 1)

fun bind' free_vars =
    List.foldl
        (fn (free_var, acc) =>
            compose (bind free_var) (compose shift acc))
        ident
        free_vars

fun unbind (t : t) free_var (Internal_var.Free_var free_var') =
    shift (t (Internal_var.Free_var free_var'))
  | unbind (t : t) free_var (Internal_var.Bound_var bound_var) =
    case bound_var
     of 0 => Internal_var.Free_var free_var
      | _ => shift (t (Internal_var.Bound_var (bound_var - 1)))

fun unbind' t free_vars =
    List.foldl (fn (free_var, acc) => unbind acc free_var) t free_vars
end
