open! Core

type ('subst, 'oper) t =
  | Var of Internal_var.t
  | Oper of 'subst * 'oper

val apply_subst
  :  apply_to_var:('subst -> Internal_var.t -> ('subst, 'oper) t)
  -> 'subst
  -> ('subst, 'oper) t
  -> ('subst, 'oper) t
