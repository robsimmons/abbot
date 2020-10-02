open! Core

type 'oper t = Renaming.t * 'oper

val apply_renaming : Renaming.t -> 'oper t -> 'oper t
