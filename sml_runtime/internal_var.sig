signature INTERNAL_VAR = sig
  datatype t = Free_var of Temp.t
             | Bound_var of int
end
