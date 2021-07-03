open! Core

module External_abts = External_abts
module Internal_var = Internal_var
module Generic_sort_and_subst = Generic_sort_and_subst
module Sort_intf = Sort_intf
module Temp = Temp
module Temp_intf = Temp_intf

type 'a compare_ignore = 'a [@@deriving sexp]
let compare_compare_ignore _ _ _ = 0
