open! Core

type 'oper t =
  | Var of Internal_var.t
  | Oper of 'oper With_renaming.t

let apply_renaming renaming = function
  | Var var -> Var (Renaming.apply renaming var)
  | Oper with_renaming ->
    Oper (With_renaming.apply_renaming renaming with_renaming)
;;
