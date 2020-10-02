open! Core

type 'oper t = Renaming.t * 'oper

let apply_renaming renaming (renaming', oper) =
  (Renaming.compose renaming renaming', oper)
;;
