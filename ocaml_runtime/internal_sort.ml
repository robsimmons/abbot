open! Core

type 'oper t =
  | Var of Internal_var.t
  | Oper of 'oper With_renaming.t

let apply_renaming renaming = function
  | Var var -> Var (Renaming.apply renaming var)
  | Oper (renaming', oper) -> Oper (Renaming.compose renaming renaming', oper)
