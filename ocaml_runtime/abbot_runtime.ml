open! Core

module External_abts = External_abts
module Internal_sort = Internal_sort
module Internal_var = Internal_var
module Renaming = Renaming
module Temp = Temp
module Temp_intf = Temp_intf
module With_renaming = With_renaming

type 'a compare_ignore = 'a [@@deriving sexp]
let compare_compare_ignore _ _ _ = 0
