open! Core

val loc : Location.t

val lident : string -> Ppxlib.longident Ppxlib.loc

val ident : 'a -> 'a Ppxlib.loc

val eident : string -> Ppxlib.expression

val pvar : string -> Ppxlib.pattern

val type_t : via_module:bool -> ?args:Ppxlib.core_type list -> string -> Ppxlib.core_type

val type_var : via_module:bool -> string -> Ppxlib.core_type

val internal_type_of_abt
  :  refer_to_via_module:(string -> bool)
  -> lang:[ `Ocaml | `Sml ]
  -> 'a Typed.Abt.t
  -> Ppxlib.core_type

val exposed_type_of_abt
  :  use_temp_directly:bool
  -> refer_to_via_module:(string -> bool)
  -> 'a Typed.Abt.t
  -> Ppxlib.core_type

val deriving_sexp_attribute : Ppxlib.attribute

val type_decl_of_cases
  :  type_of_abt:('a Typed.Abt.t -> Ppxlib.core_type)
  -> ?extra_cases:Ppxlib.constructor_declaration list
  -> deriving_sexp:bool
  -> name:string
  -> (string * 'a Typed.Abt.t option) list
  -> Ppxlib.type_declaration

val view_conversion_intf : Ppxlib.signature_item list

val convenient_constructors_intf
  :  keywords:String.Set.t
  -> type_of_abt:('a Typed.Abt.t -> Ppxlib.core_type)
  -> is_sort:bool
  -> (string * 'a Typed.Abt.t option) list
  -> Ppxlib.signature_item list

val convenient_constructors_impl
  :  keywords:String.Set.t
  -> is_sort:bool
  -> (string * 'a Typed.Abt.t option) list
  -> Ppxlib.structure_item list

val internal_error_message : Ppxlib.expression

module Walks
    (Config : sig
       val use_flat_names_internally : bool
       val qualify_constructors : bool
       val raise_internal_error_expr : Ppxlib.expression
     end)
  : sig
    val apply_renaming_code_for_simple_cases
      :  renaming:Ppxlib.expression
      -> acc:Ppxlib.expression
      ->  (string * [ `Simple ] Typed.Abt.t option) list
      -> Ppxlib.case list * [ `Used_renaming | `Ignored_renaming ]

    val into_code_for_open_cases
      :  name_of_walked_value:string
      -> (string * [ `Open ] Typed.Abt.t option) list
      -> Ppxlib.case list

    val into_code_for_closed_cases
      :  name_of_walked_value:string
      -> (string * [ `Closed ] Typed.Abt.t option) list
      -> Ppxlib.case list

    val out_code_for_open_cases
      :  name_of_walked_value:string
      -> (string * [ `Open ] Typed.Abt.t option) list
      -> Ppxlib.case list

    val out_code_for_closed_cases
      :  name_of_walked_value:string
      -> (string * [ `Closed ] Typed.Abt.t option) list
      -> Ppxlib.case list

    val subst_code_for_cases
      :  name_of_walked_value:string
      -> sub:(Ppxlib.arg_label * string) list
      -> (string * _ Typed.Abt.t option) list
      -> Ppxlib.case list * [ `Used_sub | `Ignored_sub ]
  end
