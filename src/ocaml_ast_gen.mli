open! Core

val gen_ast
  :  module_name:string
  -> Typed.Defn.t list
  -> Ppxlib.Parsetree.structure * Ppxlib.Parsetree.structure
