open! Core

type ('subst, 'oper) t =
  | Var of Internal_var.t
  | Oper of 'subst * 'oper

let rec apply_subst ~apply_to_var subst = function
  | Var var -> apply_to_var subst var
  | Oper (subst', oper) ->
    Oper (Substitution.compose ~apply:(apply_subst ~apply_to_var) subst subst', oper)
;;
