structure Internal_sort :> INTERNAL_SORT = struct
datatype 'oper t = Var of Internal_var.t
                 | Oper of 'oper With_renaming.t

fun apply_renaming renaming (Var var) =
    Var (Renaming.apply renaming var)
  | apply_renaming renaming (Oper (renaming', oper)) =
    Oper (Renaming.compose renaming renaming', oper)
end
