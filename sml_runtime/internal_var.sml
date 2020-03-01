structure Internal_var :> INTERNAL_VAR = struct
  datatype t = Free_var of Temp.t
             | Bound_var of int
end
