structure Renaming :> RENAMING = struct
type t = Internal_var.t -> Internal_var.t

fun apply t = t

fun ident var = var

fun compose t1 t2 var = t1 (t2 var)

fun bind free_var (Internal_var.Bound_var bound_var) = Internal_var.Bound_var (bound_var + 1)
  | bind free_var (Internal_var.Free_var free_var') =
    case Temp.eq (free_var, free_var')
     of true => Internal_var.Bound_var 0
      | false => Internal_var.Free_var free_var'

fun bind' free_vars =
    List.foldl
        (fn (free_var, acc) => compose (bind free_var) acc)
        ident
        free_vars

fun unbind free_var (Internal_var.Free_var free_var') = Internal_var.Free_var free_var'
  | unbind free_var (Internal_var.Bound_var bound_var) =
    case bound_var
     of 0 => Internal_var.Free_var free_var
      | _ => Internal_var.Bound_var (bound_var - 1)

fun unbind' free_vars =
    List.foldl
        (fn (free_var, acc) => compose acc (unbind free_var))
        ident
        free_vars
end
