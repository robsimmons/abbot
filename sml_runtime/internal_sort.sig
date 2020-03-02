signature INTERNAL_SORT = sig
    datatype 'oper t = Var of Internal_var.t
                     | Oper of 'oper With_renaming.t

    val apply_renaming : Renaming.t -> 'oper t -> 'oper t
end
