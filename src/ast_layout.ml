open! Core
open Ppxlib

let module_type_keyword lang =
  match lang with
  | `Ocaml -> "module type"
  | `Sml -> "signature"
;;

let module_keyword lang =
  match lang with
  | `Ocaml -> "module"
  | `Sml -> "structure"
;;

let with_type_keyword lang =
  match lang with
  | `Ocaml -> "with type"
  | `Sml -> "where type"
;;

let with_module_keyword lang =
  match lang with
  | `Ocaml -> "with module"
  | `Sml -> "where"
;;

(* CR wduff: Length 1 things (and maybe length 2 things) should maybe never be split from the next
   line. Should this code be responsible for that? Presumably the to_string phase could do it since
   it can just measure the string length. *)

let string_of_lident { txt; loc = _ } =
  let rec string_of_lident lident =
    match lident with
    | Lident string -> string
    | Ldot (lident, field) -> string_of_lident lident ^ "." ^ field
    | Lapply (_, _) ->
      raise_s [%message "unsupported lond ident"]
  in
  string_of_lident txt
;;

let atom = Layout.atom
let list = Layout.list
let always_split_list = Layout.always_split_list
let if_fits_on_line = Layout.if_fits_on_line

open Layout.Indentation

let lparen = atom ~magnet_right:true "("
let rparen = atom ~magnet_left:true ")"
let comma = atom ~magnet_left:true ","

let layout_tuple fields =
  list
    ((No_indent, lparen)
     :: List.intersperse ~sep:(No_indent, comma)
          (List.map fields ~f:(fun field -> (Indent, field)))
     @ [ (No_indent, rparen) ])
;;

let rec layout_core_type
          ~outer_precedence
          ({ ptyp_desc; ptyp_attributes = _; ptyp_loc = _; ptyp_loc_stack = _ } : core_type)
  =
  match ptyp_desc with
  | Ptyp_any -> atom "_"
  | Ptyp_var name -> atom ("'" ^ name)
  | Ptyp_arrow (label, arg_type, result_type) ->
    let add_parens =
      match outer_precedence with
      | `Space | `Pound | `Star | `Arrow -> true
      | `As | `None -> false
    in
    let rec collect_arrows rev_arg_types result_type =
        match result_type.ptyp_desc with
        | Ptyp_arrow (label, arg_type, result_type) ->
          collect_arrows ((label, arg_type) :: rev_arg_types) result_type
        | _ ->
          (List.rev rev_arg_types, result_type)
    in
    let (other_arg_types, result_type) = collect_arrows [] result_type in
    let arrow_type =
      list
        ((No_indent,
          (match label with
           | Nolabel -> layout_core_type ~outer_precedence:`Arrow arg_type
           | Labelled label ->
             list
               [ (No_indent, atom ~magnet_right:true (label ^ ":"))
               ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
               ]
           | Optional label ->
             list
               [ (No_indent, atom ~magnet_right:true ("?" ^ label ^ ":"))
               ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
               ]))
         :: List.map other_arg_types ~f:(fun (label, arg_type) ->
           (No_indent,
            list
              [ (No_indent, atom "->")
              ; (No_indent,
                 (match label with
                  | Nolabel -> layout_core_type ~outer_precedence:`Arrow arg_type
                  | Labelled label ->
                    list
                      [ (No_indent, atom ~magnet_right:true (label ^ ":"))
                      ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
                      ]
                  | Optional label ->
                    list
                      [ (No_indent, atom ~magnet_right:true ("?" ^ label ^ ":"))
                      ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
                      ]))
              ]))
         @ [ (No_indent,
              list
                [ (No_indent, atom "->")
                ; (No_indent, layout_core_type ~outer_precedence:`Arrow result_type)
                ])
           ])
    in
    begin
      match add_parens with
      | false -> arrow_type
      | true -> list [ (No_indent, lparen); (Indent, arrow_type); (No_indent, rparen) ]
    end
  | Ptyp_tuple fields ->
    begin
      match fields with
      | [] -> raise_s [%message "unsupported tuple type"]
      | field :: fields ->
        let add_parens =
          match outer_precedence with
          | `Space | `Pound | `Star -> true
          | `Arrow | `As | `None -> false
        in
        let tuple_type = layout_product_type field fields in
        match add_parens with
        | false -> tuple_type
        | true -> list [ (No_indent, lparen); (Indent, tuple_type); (No_indent, rparen) ]
    end
  | Ptyp_constr (constructor, args) ->
    begin
      match args with
      | [] -> atom (string_of_lident constructor)
      | [arg] ->
        (* CR wduff: The indentation here is weird, but it isn't clear if there is a good option. *)
        list
          [ (Indent, layout_core_type ~outer_precedence:`Space arg)
          ; (No_indent, atom (string_of_lident constructor)) ]
      | _::_::_ ->
        list
          [ (Indent,
             layout_tuple (List.map args ~f:(layout_core_type ~outer_precedence:`None)))
          ; (No_indent, atom (string_of_lident constructor))
          ]
    end
  | Ptyp_poly ([], body) -> layout_core_type ~outer_precedence:`None body
  | Ptyp_poly (_::_, _)
  | Ptyp_object _
  | Ptyp_class _
  | Ptyp_alias _
  | Ptyp_variant _
  | Ptyp_package _
  | Ptyp_extension _
    -> raise_s [%message "unsupported type7"]

and layout_product_type field fields =
  list
    ((No_indent, layout_core_type ~outer_precedence:`Star field)
     :: List.map fields ~f:(fun field ->
       (No_indent,
        list
          [ (No_indent, atom "*")
          ; (No_indent, layout_core_type ~outer_precedence:`Star field)
          ])))
;;

let layout_constant constant =
  match constant with
  | Pconst_integer (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        atom string
    end
  | Pconst_char char ->
    atom (sprintf "'%c'" char)
  | Pconst_string (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        atom (sprintf "\"%s\"" string)
    end
  | Pconst_float (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        atom string
    end
;;

let layout_attributes ~depth (attributes : attributes) =
  list
    (List.map attributes ~f:(fun { attr_name; attr_payload; attr_loc = _ } ->
       match attr_payload with
       | PStr
           [ { pstr_desc =
                 Pstr_eval ({ pexp_desc; pexp_attributes = []; pexp_loc = _; pexp_loc_stack = _ }, [])
             ; pstr_loc = _
             }
           ] ->
         let payload_layout =
           match pexp_desc with
           | Pexp_ident lident -> atom (string_of_lident lident)
           | Pexp_tuple exprs ->
             (* CR wduff: There is probably a better way to deal with these commas. *)
             list
               (List.intersperse ~sep:(No_indent, comma)
                  (List.map exprs ~f:(function
                     | { pexp_desc = Pexp_ident lident; pexp_attributes = []; pexp_loc = _; pexp_loc_stack = _ } ->
                       (Indent, atom (string_of_lident lident))
                     | _ ->
                       raise_s [%message "unsupported attribute"])))
           | Pexp_constant constant ->
             layout_constant constant
           | _ -> raise_s [%message "unsupported attribute"]
         in
         (No_indent,
          list
            [ (No_indent, atom ("[" ^ String.init depth ~f:(const '@') ^ attr_name.txt))
            ; (Indent, payload_layout)
            ; (No_indent, atom ~magnet_left:true "]")
            ])
       | _ ->
         raise_s [%message "unsupported attribute"]))
;;

let layout_field_decl { pld_name; pld_mutable; pld_type; pld_attributes = _; pld_loc = _ } =
  list
    [ (No_indent,
       (match pld_mutable with
        | Immutable -> atom pld_name.txt
        | Mutable -> list [ (No_indent, atom "mutable"); (Indent, atom pld_name.txt) ]))
    ; (Indent,
       list [ (No_indent, atom ":"); (Indent, layout_core_type ~outer_precedence:`None pld_type) ])
    ]
;;

let layout_field_defn field_name value =
  list
    [ (No_indent, list [ (No_indent, atom field_name); (No_indent, atom "=") ])
    ; (Indent, value)
    ]
;;

let layout_record field fields =
  list
    (((No_indent,
       list [ (No_indent, atom "{"); (Indent, field) ]))
     :: List.map fields ~f:(fun field ->
       (No_indent,
        list [ (No_indent, atom ~magnet_left:true ";"); (Indent, field) ]))
     @ [ (No_indent, atom "}") ])
;;

let layout_field_decls field fields =
  layout_record (layout_field_decl field) (List.map fields ~f:layout_field_decl)
;;

let layout_constructor_args (constructor_args : constructor_arguments) =
  match constructor_args with
  | Pcstr_tuple fields ->
    begin
      match fields with
      | [] -> None
      | field::fields ->
        Some (layout_product_type field fields)

    end
  | Pcstr_record fields ->
    begin
      match fields with
      | [] -> None
      | field::fields ->
        Some (layout_field_decls field fields)
    end
;;

let layout_variant_type_decl lang ~without_definition ~fits_on_line constructors =
  list
    ((No_indent, list (without_definition @ [ (No_indent, atom "=") ]))
     ::
     (List.mapi constructors
        ~f:(fun i { pcd_name; pcd_args; pcd_res; pcd_attributes = _; pcd_loc = _ } ->
          let start =
            match (lang, fits_on_line, i) with
            | (`Ocaml, true, 0) | (`Sml, _, 0) ->
              list [ (Indent, atom pcd_name.txt) ]
            | _ ->
              list [ (No_indent, atom "|"); (Indent, atom pcd_name.txt) ]
          in
          (Indent,
           match layout_constructor_args pcd_args with
           | None ->
             begin
               match pcd_res with
               | None -> start
               | Some res_type ->
                 list
                   [ (No_indent, start)
                   ; (Indent,
                      list
                        [ (No_indent, atom ":")
                        ; (Indent, layout_core_type ~outer_precedence:`None res_type)
                        ])
                   ]
             end
           | Some constructor_args ->
             begin
               match pcd_res with
               | None ->
                 list
                   [ (No_indent, start)
                   ; (Indent, list [ (No_indent, atom "of"); (Indent, constructor_args) ])
                   ]
               | Some res_type ->
                 list
                   [ (No_indent, start)
                   ; (Indent,
                      list
                        [ (No_indent, atom ":")
                        ; (Indent,
                           list
                             [ (No_indent, constructor_args)
                             ; (No_indent,
                                list
                                  [ (No_indent, atom "->")
                                  ; (No_indent,
                                     layout_core_type ~outer_precedence:`None res_type)
                                  ])
                             ])
                        ])
                   ]
             end))))
;;

let layout_type_parameter ({ ptyp_desc; ptyp_attributes = _; ptyp_loc = _; ptyp_loc_stack = _ }, variance) =
  let variance_string =
    match variance with
    | Invariant -> ""
    | Covariant -> "+"
    | Contravariant -> "-"
  in
  match ptyp_desc with
  | Ptyp_any -> atom (variance_string ^ "_")
  | Ptyp_var name -> atom (variance_string ^ "'" ^ name)
  | _ ->
    raise_s [%message "unsupported type parameter"]
;;

let layout_type_decl
      lang
      ~start_keyword
      { ptype_name
      ; ptype_params
      ; ptype_cstrs = _
      ; ptype_kind
      ; ptype_private = _
      ; ptype_manifest
      ; ptype_attributes
      ; ptype_loc = _
      }
  =
  match (lang, ptype_manifest, ptype_kind) with
  | (`Sml, Some core_type, Ptype_variant _) ->
    begin
      match ptype_params with
      | _::_ ->
        raise_s [%message "Sml datatype redefinitions shouldn't have parameters."]
      | [] ->
        list
          [ (No_indent,
             list
               [ (No_indent, atom start_keyword)
               ; (Indent, atom ptype_name.txt)
               ; (No_indent, atom "=")
               ])
          ; (Indent,
             list
               [ (No_indent, atom "datatype")
               ; (Indent, layout_core_type ~outer_precedence:`None core_type)
               ])
          ]
    end
  | _ ->
    let name_and_params =
      match ptype_params with
      | [] -> atom ptype_name.txt
      | [param] -> list [ (Indent, layout_type_parameter param); (No_indent, atom ptype_name.txt)]
      | _::_ ->
        list
          [ (Indent, layout_tuple (List.map ptype_params ~f:(layout_type_parameter)))
          ; (No_indent, atom ptype_name.txt)
          ]
    in
    let without_definition =
      match ptype_manifest with
      | None -> [ (No_indent, atom start_keyword); (Indent, name_and_params) ]
      | Some core_type ->
        [ (No_indent,
           list [ (No_indent, atom start_keyword); (Indent, name_and_params); (No_indent, atom "=") ])
        ; (Indent, layout_core_type ~outer_precedence:`None core_type)
        ]
    in
    let without_attributes =
      match ptype_kind with
      | Ptype_abstract -> list without_definition
      | Ptype_open -> list (without_definition @ [ (No_indent, atom "="); (Indent, atom "..") ])
      | Ptype_variant constructors ->
        if_fits_on_line
          ~then_:(layout_variant_type_decl lang ~without_definition ~fits_on_line:true constructors)
          ~else_:(layout_variant_type_decl lang ~without_definition ~fits_on_line:false constructors)
      | Ptype_record fields ->
        begin
          match fields with
          | [] -> raise_s [%message "unsupported record type declaration"]
          | field :: fields -> layout_field_decls field fields
        end
    in
    match ptype_attributes with
    | [] -> without_attributes
    | _::_ ->
      list
        [ (No_indent, without_attributes)
        ; (No_indent, layout_attributes ~depth:2 ptype_attributes)
        ]
;;

let layout_type_decls' lang ~first_start_keyword type_decls =
  match type_decls with
  | [] -> []
  | decl :: decls ->
    (No_indent, layout_type_decl lang ~start_keyword:first_start_keyword decl)
    :: List.map decls ~f:(fun decl ->
      (No_indent, layout_type_decl lang ~start_keyword:"and" decl))
;;

let layout_type_decls lang rec_flag type_decls =
  match lang with
  | `Ocaml ->
    let first_start_keyword =
      match rec_flag with
      | Recursive -> "type"
      | Nonrecursive -> "type nonrec"
    in
    always_split_list (layout_type_decls' lang ~first_start_keyword type_decls)
  | `Sml ->
    let (datatype_decls, type_alias_decls) =
      List.partition_tf type_decls ~f:(fun type_decl ->
        match type_decl.ptype_kind with
        | Ptype_variant _ -> true
        | _ -> false)
    in
    match datatype_decls with
    | [] ->
      always_split_list (layout_type_decls' lang ~first_start_keyword:"type" type_alias_decls)
    | _::_ ->
      always_split_list
        (layout_type_decls' lang ~first_start_keyword:"datatype" datatype_decls
         @ layout_type_decls' lang ~first_start_keyword:"withtype" type_alias_decls)
;;

let layout_open_desc
      lang
      ({ popen_expr; popen_override; popen_attributes = _; popen_loc = _ } : open_description)
  =
  match lang with
  | `Sml -> raise_s [%message "open is not supported in sml."]
  | `Ocaml ->
    let open_keyword =
      match popen_override with
      | Override -> "open!"
      | Fresh -> "open"
    in
    list [ (No_indent, atom open_keyword); (Indent, atom (string_of_lident popen_expr)) ]
;;

let layout_constraint ?(sep = ":") value typ =
  list
    [ (No_indent, list [ (No_indent, lparen); (Indent, value) ])
    ; (Indent, list [ (No_indent, atom sep); (Indent, typ); (No_indent, rparen) ])
    ]
;;

let rec layout_module_type lang ({ pmty_desc; pmty_attributes = _; pmty_loc = _ } : module_type) =
  match pmty_desc with
  | Pmty_ident lident -> atom (string_of_lident lident)
  | Pmty_signature signature ->
    list [ (No_indent, atom "sig"); (Indent, layout_signature lang signature); (No_indent, atom "end") ]
  | Pmty_functor (arg, result_type) ->
    (* CR wduff: Should we lift "sig" here as well? Is there some generic way to lift it everywhere? *)
    list
      [ (No_indent,
         list
           [ (No_indent, atom "functor")
           ; (Indent, layout_functor_parameter lang arg)
           ; (No_indent, atom "->")
           ])
      ; (Indent, layout_module_type lang result_type)
      ]
  | Pmty_with (module_type, with_constraints) ->
    list
      ((No_indent, layout_module_type lang module_type)
       :: List.map with_constraints ~f:(fun with_constraint ->
         (* CR wduff: Handle params in the type cases, and check that weird stuff doesn't show up in
            the type declarations. *)
         (Indent,
          match with_constraint with
          | Pwith_type (lident, type_decl) ->
            list
              [ (No_indent,
                 list
                   [ (No_indent, atom (with_type_keyword lang))
                   ; (Indent,
                      (match type_decl.ptype_params with
                       | [] -> atom (string_of_lident lident)
                       | _::_ ->
                         list
                           [ (Indent,
                              list
                                [ (No_indent, lparen)
                                ; (Indent,
                                   list
                                     (List.map type_decl.ptype_params ~f:(fun (param, _variance) ->
                                        (No_indent,
                                         layout_core_type ~outer_precedence:`None param))
                                      |> List.intersperse ~sep:(No_indent, comma)))
                                ; (No_indent, rparen)
                                ])
                           ; (No_indent, atom (string_of_lident lident))
                           ]))
                   ; (No_indent, atom "=")
                   ])
              ; (Indent,
                 layout_core_type
                   ~outer_precedence:`None
                   (Option.value_exn type_decl.ptype_manifest))
              ]
          | Pwith_module (lident1, lident2) ->
            list
              [ (No_indent,
                 list
                   [ (No_indent, atom (with_module_keyword lang))
                   ; (Indent, atom (string_of_lident lident1))
                   ; (No_indent, atom "=")
                   ])
              ; (Indent, atom (string_of_lident lident2))
              ]
          | Pwith_typesubst (lident, type_decl) ->
            list
              [ (No_indent,
                 list
                   [ (No_indent, atom (with_type_keyword lang))
                   ; (Indent,
                      (match type_decl.ptype_params with
                       | [] -> atom (string_of_lident lident)
                       | _::_ ->
                         list
                           [ (Indent,
                              list
                                [ (No_indent, lparen)
                                ; (Indent,
                                   list
                                     (List.map type_decl.ptype_params ~f:(fun (param, _variance) ->
                                        (No_indent,
                                         layout_core_type ~outer_precedence:`None param))
                                      |> List.intersperse ~sep:(No_indent, comma)))
                                ; (No_indent, rparen)
                                ])
                           ; (No_indent, atom (string_of_lident lident))
                           ]))
                   ; (No_indent, atom ":=")
                   ])
              ; (Indent,
                 layout_core_type
                   ~outer_precedence:`None
                   (Option.value_exn type_decl.ptype_manifest))
              ]
          | Pwith_modsubst (lident1, lident2) ->
            list
              [ (No_indent,
                 list
                   [ (No_indent, atom (with_module_keyword lang))
                   ; (Indent, atom (string_of_lident lident1))
                   ; (No_indent, atom ":=")
                   ])
              ; (Indent, atom (string_of_lident lident2))
              ])))
  | Pmty_alias _ | Pmty_typeof _ | Pmty_extension _ ->
    raise_s [%message "unsupported module type"]

and layout_module_type_decl lang { pmtd_name; pmtd_type; pmtd_attributes = _; pmtd_loc = _ } =
  (* CR wduff: Special case sig ... end. *)
  match pmtd_type with
  | None -> list [ (No_indent, atom (module_type_keyword lang)); (Indent, atom pmtd_name.txt) ]
  | Some module_type ->
    let start =
      [ (No_indent, atom (module_type_keyword lang))
      ; (Indent, atom pmtd_name.txt)
      ; (No_indent, atom "=")
      ]
    in
    match module_type.pmty_desc with
    | Pmty_signature signature ->
      list
        [ (No_indent, list (start @ [ (No_indent, atom "sig") ]))
        ; (Indent, layout_signature lang signature)
        ; (No_indent, atom "end")
        ]
    | _ ->
      list
        [ (No_indent, list start)
        ; (Indent, layout_module_type lang module_type)
        ]

and layout_functor_parameter lang functor_parameter =
  match functor_parameter with
  | Unit -> atom "()"
  | Named (arg_name, arg_type) ->
    let arg_name =
      match arg_name.txt with
      | None ->
        (* CR wduff: This case is not handled well for module types. *)
        "_"
      | Some arg_name ->
        arg_name
    in
    layout_constraint (atom arg_name) (layout_module_type lang arg_type)

and layout_module_decl lang ~start_keyword { pmd_name; pmd_type; pmd_attributes = _; pmd_loc = _ } =
  let rec strip_functor_args (({ pmty_desc; pmty_attributes = _; pmty_loc = _ } as module_type) : module_type) =
    match pmty_desc with
    | Pmty_functor (arg, result_type) ->
      let (args, result_type) = strip_functor_args result_type in
      ((Indent, layout_functor_parameter lang arg) :: args, result_type)
    | _ -> ([], module_type)
  in
  let (args, result_type) = strip_functor_args pmd_type in
  let start_keyword =
    match args with
    | [] -> start_keyword
    | _::_ ->
      match lang with
      | `Ocaml -> start_keyword
      | `Sml -> "functor"
  in
  (* CR wduff: This is an interesting case: If the name gets put on a new line and indented, the
     arguments should probably be indented an extra level. *)
  match pmd_name.txt with
  | None ->
    (* What does it even mean for a module declaration to have no name? *)
    raise_s [%message "unsupported signature item"]
  | Some name ->
    let start =
      (No_indent, list [ (No_indent, atom start_keyword); (Indent, atom name) ]) :: args
    in
    (* CR wduff: Shouldn't the colon by default be on the next line? *)
    match result_type.pmty_desc with
    | Pmty_signature signature ->
      list
        [ (No_indent, list (start @ [ (No_indent, atom ":"); (No_indent, atom "sig") ]))
        ; (Indent, layout_signature lang signature)
        ; (No_indent, atom "end")
        ]
    | Pmty_alias lident ->
      list
        [ (No_indent, list (start @ [ (No_indent, atom "=") ]))
        ; (Indent, atom (string_of_lident lident))
        ]
    | _ ->
      list
        [ (No_indent, list start)
        ; (Indent, list [ (No_indent, atom ":"); (Indent, layout_module_type lang result_type) ])
        ]

and layout_signature_item lang ({ psig_desc; psig_loc = _ } : signature_item) =
  match psig_desc with
  | Psig_value { pval_name; pval_type; pval_prim; pval_attributes = _; pval_loc = _ } ->
    begin
      match pval_prim with
      | [] -> ()
      | _::_ -> raise_s [%message "unsupported signature item"]
    end;
    list
      [ (No_indent, list [ (No_indent, atom "val"); (Indent, atom pval_name.txt) ])
      ; (Indent,
         list
           [ (No_indent, atom ":"); (Indent, layout_core_type ~outer_precedence:`None pval_type) ])
      ]
  | Psig_type (rec_flag, type_decls) ->
    layout_type_decls lang rec_flag type_decls
  | Psig_module decl ->
    layout_module_decl lang ~start_keyword:(module_keyword lang) decl
  | Psig_recmodule module_decls ->
    begin
      match lang with
      | `Sml ->
        raise_s [%message "Recursive modules are not supported in sml."]
      | `Ocaml ->
        match module_decls with
        | [] ->
          raise_s [%message "Got empty list of recursive modules."]
        | decl :: decls ->
          list
            ((No_indent, layout_module_decl lang ~start_keyword:"module rec" decl)
             :: List.map decls ~f:(fun decl ->
               (No_indent, layout_module_decl lang ~start_keyword:"and" decl)))
    end
  | Psig_modtype module_type_decl ->
    layout_module_type_decl lang module_type_decl
  | Psig_open open_description ->
    layout_open_desc lang open_description
  | Psig_include { pincl_mod; pincl_attributes = _; pincl_loc = _ } ->
    list [ (No_indent, atom "include"); (Indent, layout_module_type lang pincl_mod) ]
  | Psig_extension (extension, _) ->
    begin
      match extension with
      | ({ txt = "sharing_type"; loc = _ },
         PTyp { ptyp_desc = Ptyp_tuple [ type1; type2 ]; ptyp_attributes = _; ptyp_loc = _; ptyp_loc_stack = _ })
        ->
        list
          [ (No_indent, atom "sharing type")
          ; (Indent,
             list
               [ (No_indent, layout_core_type ~outer_precedence:`None type1)
               ; (No_indent, atom "=")
               ; (No_indent, layout_core_type ~outer_precedence:`None type2)
               ])
          ]
      | _ ->
        raise_s [%message "unsupported signature item"]
    end
  | Psig_typext _
  | Psig_exception _
  | Psig_class _
  | Psig_class_type _
  | Psig_attribute _
  | Psig_typesubst _
  | Psig_modsubst _
    ->
    raise_s [%message "unsupported signature item"]

and layout_signature lang signature =
  list
    (List.map signature ~f:(fun signature_item ->
       (No_indent, layout_signature_item lang signature_item)))
;;

let can_pun_pattern string { ppat_desc; _ } =
  match ppat_desc with
  | Ppat_var { txt = string'; loc = _ } -> String.equal string string'
  | _ -> false
;;

let can_pun_expression string { pexp_desc; _ } =
  match pexp_desc with
  | Pexp_ident { txt = (Lident string'); loc = _ } -> String.equal string string'
  | _ -> false
;;

let layout_arg ~layout ~can_pun arg_label arg =
  match arg_label with
  | Nolabel -> layout arg
  | Labelled label ->
    begin
      match can_pun label arg with
      | true -> atom ("~" ^ label)
      | false ->
        list [ (No_indent, atom ~magnet_right:true ("~" ^ label ^ ":")); (Indent, layout arg) ]
    end
  | Optional label ->
    begin
      match can_pun label arg with
      | true -> atom ("?" ^ label)
      | false ->
        list [ (No_indent, atom ~magnet_right:true ("?" ^ label ^ ":")); (Indent, layout arg) ]
    end
;;

let rec layout_pattern lang ~outer_precedence { ppat_desc; ppat_attributes = _; ppat_loc = _; ppat_loc_stack = _ } =
  match ppat_desc with
  | Ppat_any -> atom "_"
  | Ppat_var name -> atom name.txt
  | Ppat_alias (pat, alias) ->
    list
      [ (No_indent, layout_pattern lang ~outer_precedence:`As pat)
      ; (No_indent, list [ (No_indent, atom "as"); (No_indent, atom alias.txt) ])
      ]
  | Ppat_constant constant -> layout_constant constant
  | Ppat_interval (constant1, constant2) ->
    list
      [ (No_indent, layout_constant constant1)
      ; (No_indent, list [ (No_indent, atom ".."); (No_indent, layout_constant constant2) ])
      ]
  | Ppat_tuple pats ->
    layout_tuple (List.map pats ~f:(layout_pattern ~outer_precedence:`Tuple_elt lang))
  | Ppat_construct (constructor, pat_opt) ->
    begin
      match pat_opt with
      | None -> atom (string_of_lident constructor)
      | Some pat ->
        let include_parens =
          match outer_precedence with
          | `None | `As | `Or | `Constrained | `Record_elt | `Tuple_elt -> false
          | `Force_parens | `Fun_arg | `Constr_arg -> true
        in
        list
          [ (No_indent,
             list
               ((match include_parens with
                  | false -> []
                  | true -> [ (No_indent, lparen) ])
                @
               [ (Indent, atom (string_of_lident constructor)) ]))
          ; (Indent,
             list
               ([ (No_indent, layout_pattern lang ~outer_precedence:`Constr_arg pat) ]
                @
                (match include_parens with
                 | false -> []
                 | true -> [ (No_indent, rparen) ])))
          ]
    end
  | Ppat_record (fields, closed_flag) ->
    begin
      match
        List.map fields ~f:(fun (lident, pat) ->
          layout_field_defn
            (string_of_lident lident)
            (layout_pattern lang ~outer_precedence:`Record_elt pat))
        @ (match closed_flag with
          | Closed -> []
          | Open -> [ atom "_" ])
      with
      | [] ->
        raise_s [%message "Got empty record."]
      | field :: fields ->
        layout_record field fields
    end
  | Ppat_or (pat1, pat2) ->
    (* CR wduff: This surely needs parens sometimes. *)
    list
      [ (No_indent, layout_pattern lang ~outer_precedence:`Or pat1)
      ; (No_indent,
         list
           [ (No_indent, atom "|")
           ; (Indent, layout_pattern lang ~outer_precedence:`Or pat2)
           ])
      ]
  | Ppat_constraint (pat, core_type) ->
    layout_constraint
      (layout_pattern lang ~outer_precedence:`Constrained pat)
      (layout_core_type ~outer_precedence:`None core_type)
  | Ppat_variant _
  | Ppat_array _
  | Ppat_type _
  | Ppat_lazy _
  | Ppat_unpack _
  | Ppat_exception _
  | Ppat_extension _
  | Ppat_open _
    ->
    raise_s [%message "unsupported pattern"]
;;

(* CR wduff: Do something similar to this for patterns. *)
let rec try_to_get_list_elements expr =
  match expr.pexp_desc with
  | Pexp_tuple [ head; { pexp_desc = Pexp_construct ({ txt = Lident "[]"; _ }, arg_opt); _ } ] ->
    begin
      match arg_opt with
      | Some _ -> None
      | None ->
        Some (head, [])
    end
  | Pexp_tuple [ head; { pexp_desc = Pexp_construct ({ txt = Lident "::"; _ }, arg_opt); _ } ] ->
    begin
      match arg_opt with
      | None -> None
      | Some arg ->
        match try_to_get_list_elements arg with
        | None -> None
        | Some (tail_head, tail_tail) ->
          Some (head, tail_head :: tail_tail)
    end
  | _ ->
    None

let layout_arg' ~lang arg_label default_opt arg_pat =
  match default_opt with
  | Some _ ->
    raise_s [%message "unsupported expression"]
  | None ->
    layout_arg
      ~layout:(layout_pattern lang ~outer_precedence:`Fun_arg)
      ~can_pun:can_pun_pattern
      arg_label
      arg_pat
;;

let rec strip_function_args ~lang expr =
  match expr.pexp_desc with
  | Pexp_newtype (type_name, body) ->
    let layout = atom (sprintf "(type %s)" type_name.txt) in
    let (other_args, body) = strip_function_args ~lang body in
    (layout :: other_args, body)
  | Pexp_fun (arg_label, default_opt, arg_pat, body) ->
    let layout = layout_arg' ~lang arg_label default_opt arg_pat in
    let (other_args, body) = strip_function_args ~lang body in
    (layout :: other_args, body)
  | _ -> ([], expr)
;;


(* CR wduff: Are the precedence rules right for sml? *)
(* CR wduff: Fix the way parens work here. Remove superfluous ones, add needed ones, and maybe use
   begin ... end for multi line stuff in the ocaml case. *)
let rec layout_expression lang ~outer_precedence expr =
  match expr.pexp_desc with
  | Pexp_ident lident -> atom (string_of_lident lident)
  | Pexp_constant constant -> layout_constant constant
  | Pexp_let (rec_flag, value_bindings, body) ->
    (* CR wduff: The structure of this code can probably be shared with other code. *)
    begin
      match value_bindings with
      | [] ->
        (* CR wduff: Better error. *)
        raise_s [%message "wtf"]
      | binding :: bindings ->
        let include_parens =
          match outer_precedence with
          | `None | `Let_body | `Fun_body | `Match | `Constrained | `Case_rhs -> false
          | `Force_parens
          | `Sequence_elt
          | `list_elt
          | `Record_elt
          | `Tuple_elt
          | `Infix_arg
          | `Fun
          | `Fun_arg
            ->
            true
        in
        let value_binding_indentation =
          match lang with
          | `Ocaml -> No_indent
          | `Sml -> Indent
        in
        list
          ([ (No_indent,
              list
                ((match (lang, include_parens) with
                   | (`Ocaml, false) -> []
                   | (`Ocaml, true) -> [ (No_indent, lparen) ]
                   | (`Sml, false) -> [ (No_indent, atom "let") ]
                   | (`Sml, true) -> [ (No_indent, atom "(let") ])
                 @
                 [ (value_binding_indentation,
                    layout_value_binding lang rec_flag ~is_first_in_group:true binding)
                 ]
                 @
                 List.map bindings ~f:(fun binding ->
                   (value_binding_indentation,
                    layout_value_binding lang rec_flag ~is_first_in_group:false binding))
                 (* CR wduff: Is this the right way to deal with "in"? *)
                 @
                 [ (No_indent, atom "in") ]))
           ; (No_indent,
              list
                ([ (No_indent,
                    layout_expression lang ~outer_precedence:`Let_body body) ]
                 @
                 (match (lang, include_parens) with
                  | (`Ocaml, false) -> []
                  | (`Ocaml, true) -> [ (No_indent, rparen) ]
                  | (`Sml, false) -> [ (No_indent, atom "end") ]
                  | (`Sml, true) -> [ (No_indent, atom "end)") ])))
           ])
    end
  | Pexp_function cases ->
    begin
      match lang with
      | `Sml -> raise_s [%message "unsupported expression in sml"]
      | `Ocaml ->
        let include_parens =
          match outer_precedence with
          | `None | `Let_body | `Fun_body | `Match | `Constrained | `Case_rhs ->
            false
          | `Force_parens
          | `Sequence_elt
          | `list_elt
          | `Record_elt
          | `Tuple_elt
          | `Infix_arg
          | `Fun
          | `Fun_arg
            ->
            true
        in
        (* CR wduff: Support this case. *)
        assert (not include_parens);
        list
          ((No_indent, atom "function")
           :: List.mapi cases ~f:(fun i case ->
             (No_indent, layout_match_case lang ~first_case:(Int.equal i 0) case)))
    end
  | Pexp_fun _ | Pexp_newtype _ ->
    let (args, body) =
      match lang with
      | `Ocaml -> strip_function_args ~lang expr
      | `Sml ->
        match expr.pexp_desc with
        | Pexp_fun (arg_label, default_opt, arg_pat, body) ->
          ([ layout_arg' ~lang arg_label default_opt arg_pat ], body)
        | Pexp_newtype _ ->
          raise_s [%message "unsupported expression in sml"]
        | _ -> assert false
    in
    begin
      (* CR wduff: Drop parens sometimes? Maybe if it is the entire expression or something? *)
      list
        [ (No_indent,
           list
             [ (No_indent,
                atom
                  (match lang with
                   | `Ocaml -> "(fun"
                   | `Sml -> "(fn"))
             ; (Indent,
                list
                  (List.map args ~f:(fun layout -> (No_indent, layout))))
             ; (No_indent,
                atom
                  (match lang with
                   | `Ocaml -> "->"
                   | `Sml -> "=>"))
             ])
        ; (Indent, layout_expression lang ~outer_precedence:`Fun_body body)
        ; (No_indent, rparen)
        ]
    end
  | Pexp_apply (func, args) ->
    let is_infix =
      match func.pexp_desc with
      | Pexp_ident lident ->
        begin
          match string_of_lident lident with
          | "*" | "+" | "-" | "-." | "=" | "!=" | "<" | ">" | "or" | "||" | "&" | "&&" | ":="
          | "mod" | "land" | "lor" | "lxor" | "lsl" | "lsr" | "asr" as oper ->
            Some oper
          | "" ->
            None
          | ident ->
            match ident.[0] with
            | '=' | '<' | '>' | '@' | '^' | '|' | '&' | '+' | '-' | '*' | '/' | '$' | '%' ->
              Some ident
            | _ -> None
        end
      | _ ->
        None
    in
    begin
      match is_infix with
      | None ->
        let include_parens =
          match outer_precedence with
          | `None
          | `Let_body
          | `Fun_body
          | `Match
          | `Constrained
          | `Case_rhs
          | `Sequence_elt
          | `list_elt
          | `Record_elt
          | `Tuple_elt
          | `Infix_arg
            ->
            false
          | `Force_parens | `Fun | `Fun_arg ->
            true
        in
        list
          ((match include_parens with
             | false ->  []
             | true -> [ (No_indent, lparen) ])
           @
           [ (No_indent, layout_expression lang ~outer_precedence:`Fun func) ]
           @
           List.map args ~f:(fun (arg_label, arg) ->
             (Indent,
              layout_arg
                ~layout:(layout_expression lang ~outer_precedence:`Fun_arg)
                ~can_pun:can_pun_expression
                arg_label
                arg))
           @
           (match include_parens with
            | false -> []
            | true -> [ (No_indent, rparen) ]))
      | Some oper ->
        begin
          match args with
          | [] ->
            (* CR wduff: Better error. *)
            raise_s [%message "wtf"]
          | (arg_label, arg) :: args ->
            (* CR wduff: This is bad formatting. *)
            (* CR wduff: At some point we could keep track of *which* infix operator the expression
               is an argument of, but the extra parens often improve readability. *)
            let include_parens =
              match outer_precedence with
              | `None
              | `Let_body
              | `Fun_body
              | `Match
              | `Constrained
              | `Case_rhs
              | `Sequence_elt
              | `list_elt
              | `Record_elt
              | `Tuple_elt
                ->
                false
              | `Force_parens | `Infix_arg | `Fun | `Fun_arg ->
                true
            in
            list
              ((match include_parens with
                 | false -> []
                 | true -> [ (No_indent, lparen) ])
               @
               [ (No_indent,
                  layout_arg
                    ~layout:(layout_expression lang ~outer_precedence:`Infix_arg)
                    ~can_pun:can_pun_expression
                    arg_label
                    arg)
               ; (No_indent, atom oper)
               ]
               @
               List.map args ~f:(fun (arg_label, arg) ->
                 (Indent,
                  layout_arg
                    ~layout:(layout_expression lang ~outer_precedence:`Infix_arg)
                    ~can_pun:can_pun_expression
                    arg_label
                    arg))
               @
               (match include_parens with
                | false -> []
                | true -> [ (No_indent, rparen) ]))
        end
    end
  | Pexp_match (expr, cases) ->
    (* CR wduff: Drop parens sometimes? Maybe if it is the entire expression or something? *)
    let include_parens =
      match outer_precedence with
      | `None
      | `Let_body
      | `Fun_body
      | `Match
      | `Constrained
        ->
        false
      | `Case_rhs
      | `Sequence_elt
      | `list_elt
      | `Record_elt
      | `Tuple_elt
      | `Force_parens
      | `Infix_arg
      | `Fun
      | `Fun_arg
        ->
        true
    in
    list
      ((No_indent,
        list
          [ (No_indent,
             atom
               (match (lang, include_parens) with
                | (`Ocaml, false) -> "match"
                | (`Ocaml, true) -> "(match"
                | (`Sml, false) -> "case"
                | (`Sml, true) -> "(case"))
          ; (Indent, layout_expression lang ~outer_precedence:`Match expr)
          ; (No_indent,
             atom
               (match lang with
                | `Ocaml -> "with"
                | `Sml -> "of"))
          ])
       :: List.mapi cases ~f:(fun i case ->
         (No_indent, layout_match_case lang ~first_case:(Int.equal i 0) case))
       @
       (match include_parens with
        | false -> []
        | true -> [ (No_indent, rparen)]))
  | Pexp_tuple exprs ->
    layout_tuple (List.map exprs ~f:(layout_expression lang ~outer_precedence:`Tuple_elt))
  | Pexp_construct (constructor, arg_opt) ->
    let constructor = string_of_lident constructor in
    begin
      match arg_opt with
      | None -> atom constructor
      | Some arg ->
        match constructor with
        | "::" ->
          begin
            match try_to_get_list_elements arg with
            | Some (elt, elts) ->
              list
                ([ (No_indent,
                    list
                      [ (No_indent, atom "[")
                      ; (Indent, layout_expression lang ~outer_precedence:`list_elt elt)
                      ])
                 ]
                 @
                 List.map elts ~f:(fun elt ->
                   (No_indent,
                    list
                      [ (No_indent, atom (match lang with `Ocaml -> ";" | `Sml -> ","))
                      ; (Indent, layout_expression lang ~outer_precedence:`list_elt elt)
                      ]))
                 @
                 [ (No_indent, atom "]") ])
            | None ->
              match arg.pexp_desc with
              | Pexp_tuple [ head; tail ] ->
                list
                  [ (No_indent, layout_expression lang ~outer_precedence:`Infix_arg head)
                  ; (No_indent,
                     list
                       [ (No_indent, atom "::")
                       ; (No_indent, layout_expression lang ~outer_precedence:`Infix_arg tail)
                       ])
                  ]
              | _ ->
                (* CR wduff: Better error. *)
                raise_s [%message "wtf"]
          end
        | constructor ->
          let include_parens =
            match outer_precedence with
            | `None
            | `Let_body
            | `Fun_body
            | `Match
            | `Constrained
            | `Case_rhs
            | `Sequence_elt
            | `list_elt
            | `Record_elt
            | `Tuple_elt
            | `Infix_arg
              ->
              false
            | `Force_parens | `Fun | `Fun_arg ->
              true
          in
          list
            ((match include_parens with
               | false -> []
               | true -> [ (No_indent, lparen) ])
             @
             [ (No_indent, atom constructor)
             ; (Indent, layout_expression lang ~outer_precedence:`Fun_arg arg)
             ]
             @
             (match include_parens with
              | false -> []
              | true -> [ (No_indent, rparen) ]))
    end
  | Pexp_record (fields, expr_opt) ->
    begin
      match expr_opt with
      | Some _ ->
        raise_s [%message "unsupported expression"]
      | None ->
        match
          List.map fields ~f:(fun (lident, expr) ->
            layout_field_defn
              (string_of_lident lident)
              (layout_expression lang ~outer_precedence:`Record_elt expr))
        with
        | [] ->
          raise_s [%message "Got empty record."]
        | field :: fields ->
          layout_record field fields
    end
  | Pexp_sequence (expr1, expr2) ->
    let include_parens =
      match outer_precedence with
      | `None
      | `Let_body
      | `Fun_body
      | `Match
      | `Constrained
      | `Case_rhs
      | `Sequence_elt
        -> false
      | `Force_parens
      | `list_elt
      | `Record_elt
      | `Tuple_elt
      | `Infix_arg
      | `Fun
      | `Fun_arg ->
        true
    in
    list
      ((match include_parens with
         | false -> []
         | true -> [ (No_indent, lparen) ])
       @
       [ (No_indent,
          list
            [ (No_indent, layout_expression lang ~outer_precedence:`Sequence_elt expr1)
            ; (No_indent, atom ~magnet_left:true ";")
            ])
       ; (No_indent, layout_expression lang ~outer_precedence:`Sequence_elt expr2)
       ]
       @
       (match include_parens with
        | false -> []
        | true -> [ (No_indent, rparen) ]))
  | Pexp_constraint (expr, core_type) ->
    layout_constraint
      (layout_expression lang ~outer_precedence:`Constrained expr)
      (layout_core_type ~outer_precedence:`None core_type)
  | Pexp_extension extension ->
    layout_extension lang ~depth:1 extension
  | Pexp_letmodule (name_opt, modl, expr) ->
    (* CR wduff: Consider including parens? *)
    list
      [ (No_indent,
         (* CR wduff: The fact that just the in can get split off seems kinda crappy. *)
         list
           [ (No_indent, layout_module_binding' lang ~start_keyword:"let module" name_opt modl)
           ; (No_indent, atom "in")
           ])
      ; (No_indent, layout_expression lang ~outer_precedence:`Let_body expr)
      ]
  | Pexp_try _
  | Pexp_variant _
  | Pexp_field _
  | Pexp_setfield _
  | Pexp_array _
  | Pexp_ifthenelse _
  | Pexp_while _
  | Pexp_for _
  | Pexp_coerce _
  | Pexp_send _
  | Pexp_new _
  | Pexp_setinstvar _
  | Pexp_override _
  | Pexp_letexception _
  | Pexp_assert _
  | Pexp_lazy _
  | Pexp_poly _
  | Pexp_object _
  | Pexp_pack _
  | Pexp_open _
  | Pexp_letop _
  | Pexp_unreachable
    ->
    raise_s [%message "unsupported expression"]

and layout_value_binding
      lang
      (rec_flag : rec_flag)
      ~is_first_in_group
      { pvb_pat; pvb_expr; pvb_attributes = _; pvb_loc = _ }
  =
  let (args, body) =
    match pvb_pat.ppat_desc with
    | Ppat_var _ -> strip_function_args ~lang pvb_expr
    | _ -> ([], pvb_expr)
  in
  let start_keyword =
    match (List.is_empty args, rec_flag, is_first_in_group, lang) with
    | (_, Recursive, true, `Ocaml) -> "let rec"
    | (_, Nonrecursive, true, `Ocaml) -> "let"
    | (_, _, false, `Ocaml) -> "and"
    | (true, Recursive, true, `Sml) -> "val rec"
    | (true, Nonrecursive, true, `Sml) -> "val"
    | (false, _, true, `Sml) -> "fun"
    | (_, _, false, `Sml) -> "and"
  in
  let (result_type, body) =
    match body.pexp_desc with
    | Pexp_constraint (body, core_type) -> (Some core_type, body)
    | _ -> (None, body)
  in
  list
    [ (No_indent,
       list
         [ (No_indent,
            list
              ((No_indent,
                list
                  [ (No_indent, atom start_keyword)
                  ; (Indent, layout_pattern lang ~outer_precedence:`None pvb_pat)
                  ])
               ::
               List.map args ~f:(fun arg ->
                 (Indent, list [ (Indent, arg)]))))
         ; (Indent,
            (match result_type with
             | None -> atom "="
             | Some result_type ->
               list
                 [ (No_indent, atom ":")
                 ; (Indent, layout_core_type ~outer_precedence:`None result_type)
                 ; (No_indent, atom "=")
                 ]))
         ])
    ; (Indent, layout_expression lang ~outer_precedence:`None body)
    ]

and layout_extension lang ~depth (name, payload) =
  let (separator, payload_layout) =
    match payload with
    | PStr [ { pstr_desc = Pstr_eval (expr, []); pstr_loc = _ } ] ->
      ("", layout_expression lang ~outer_precedence:`None expr)
    | PTyp core_type ->
      (":", layout_core_type ~outer_precedence:`None core_type)
    | _ ->
      raise_s [%message "unsupported extension point"]
  in
  list
    [ (No_indent,
       atom
         ("["
          ^ String.init depth ~f:(const '%')
          ^ name.txt
          ^ separator))
    ; (Indent, payload_layout)
    ; (No_indent, atom ~magnet_left:true "]")
    ]

and layout_match_case
      lang
      ~first_case
      { pc_lhs; pc_guard; pc_rhs }
  =
  match pc_guard with
  | Some _ ->
    raise_s [%message "unsupported match case"]
  | None ->
    match (lang, first_case) with
    | (`Sml, true) ->
      list
        [ (No_indent,
           list
             [ (Indent, layout_pattern lang ~outer_precedence:`None pc_lhs)
             ; (No_indent,
                atom
                  (match lang with
                   | `Ocaml -> "->"
                   | `Sml -> "=>"))
             ])
        ; (Indent, layout_expression lang ~outer_precedence:`Case_rhs pc_rhs)
        ]
    | (`Sml, false) | (`Ocaml, _) ->
      (* CR wduff: Deal with or-patterns specially? *)
      list
        [ (No_indent,
           list
             [ (No_indent, atom "|")
             ; (Indent, layout_pattern lang ~outer_precedence:`None pc_lhs)
             ; (No_indent,
                atom
                  (match lang with
                   | `Ocaml -> "->"
                   | `Sml -> "=>"))
             ])
        ; (Indent, layout_expression lang ~outer_precedence:`Case_rhs pc_rhs)
        ]

and layout_module lang { pmod_desc; pmod_attributes = _; pmod_loc = _ } =
  match pmod_desc with
  | Pmod_ident lident ->
    atom (string_of_lident lident)
  | Pmod_structure structure ->
    list
      [ (No_indent, atom "struct")
      ; (Indent, layout_structure lang structure)
      ; (No_indent, atom "end")
      ]
  | Pmod_apply (module_expr1, module_expr2) ->
    list
      [ (No_indent, layout_module lang module_expr1)
      ; (Indent,
         list
           [ (No_indent, lparen)
           ; (Indent, layout_module lang module_expr2)
           ; (No_indent, rparen)
           ])
      ]
  | Pmod_constraint (module_expr, module_type) ->
    layout_constraint
      ~sep:(match lang with `Ocaml -> ":" | `Sml -> ":>")
      (layout_module lang module_expr)
      (layout_module_type lang module_type)
  | Pmod_functor _
  | Pmod_unpack _
  | Pmod_extension _
    ->
    raise_s [%message "unsupported module"]

and layout_module_binding'
      lang
      ~start_keyword
      modl_name
      modl_expr
  =
  (* CR wduff: This code is largely a duplicate of layout_module_decl. *)
  let rec strip_functor_args (({ pmod_desc; pmod_attributes = _; pmod_loc = _ } as module_expr) : module_expr) =
    match pmod_desc with
    | Pmod_functor (arg, body) ->
      let (args, body) = strip_functor_args body in
      ((Indent, layout_functor_parameter lang arg) :: args, body)
    | _ -> ([], module_expr)
  in
  let (args, body) = strip_functor_args modl_expr in
  let start_keyword =
    match args with
    | [] -> start_keyword
    | _::_ ->
      match lang with
      | `Ocaml -> start_keyword
      | `Sml -> "functor"
  in
  (* CR wduff: This is an interesting case: If the name gets put on a new line and indented, the
     arguments should probably be indented an extra level. *)
  match modl_name.txt with
  | None ->
    (* What does it even mean for a module declaration to have no name? *)
    raise_s [%message "unsupported signature item"]
  | Some name ->
    let start =
      (No_indent, list [ (No_indent, atom start_keyword); (Indent, atom name) ]) :: args
    in
    let (start, body) =
      match body.pmod_desc with
      | Pmod_constraint (module_expr, module_type) ->
        ([ (No_indent, list (start @ [ (No_indent, atom (match lang with `Ocaml -> ":" | `Sml -> ":>")) ]))
         ; (Indent, layout_module_type lang module_type)
         ; (No_indent, atom "=")
         ],
         module_expr)
      | _ ->
        (start @ [ (No_indent, atom "=") ], body)
    in
    match body.pmod_desc with
    | Pmod_structure structure ->
      list
        [ (No_indent, list (start @ [ (No_indent, atom "struct") ]))
        ; (Indent, layout_structure lang structure)
        ; (No_indent, atom "end")
        ]
    | _ ->
      list
        [ (No_indent, list start)
        ; (Indent, layout_module lang body)
        ]

and layout_module_binding
      lang
      ~start_keyword
      { pmb_name; pmb_expr; pmb_attributes = _; pmb_loc = _ }
  =
  layout_module_binding' lang ~start_keyword pmb_name pmb_expr

and layout_structure_item lang ({ pstr_desc; pstr_loc = _ } : structure_item) =
  match pstr_desc with
  | Pstr_value (rec_flag, value_bindings) ->
    (* CR wduff: The structure of this code can probably be shared with other code. *)
    begin
      match value_bindings with
      | [] ->
        (* CR wduff: Better error. *)
        raise_s [%message "wtf"]
      | binding :: bindings ->
        list
          ((No_indent, layout_value_binding lang rec_flag ~is_first_in_group:true binding)
           :: List.map bindings ~f:(fun binding ->
             (No_indent,
              layout_value_binding lang rec_flag ~is_first_in_group:false binding)))
    end
  | Pstr_type (rec_flag, type_decls) ->
    layout_type_decls lang rec_flag type_decls
  | Pstr_module module_binding ->
    layout_module_binding lang ~start_keyword:(module_keyword lang) module_binding
  | Pstr_recmodule module_bindings ->
    (* CR wduff: This code is largely a duplicate of the Psig_recmodule case. *)
    begin
      (* CR wduff: match lang with
      | `Sml ->
        raise_s [%message "Recursive modules are not supported in sml."]
      | `Ocaml ->*)
        match module_bindings with
        | [] ->
          (* CR wduff: Better error. *)
          raise_s [%message "wtf"]
        | binding :: bindings ->
          list
            ((No_indent, layout_module_binding lang ~start_keyword:"module rec" binding)
             :: List.map bindings ~f:(fun binding ->
               (No_indent,
                layout_module_binding lang ~start_keyword:"and" binding)))
    end
  | Pstr_modtype module_type_decl ->
    layout_module_type_decl lang module_type_decl
  | Pstr_open open_declaration ->
    layout_open_decl lang open_declaration
  | Pstr_include { pincl_mod; pincl_attributes = _; pincl_loc = _ } ->
    list
      [ (No_indent,
         atom
           (match lang with
            | `Ocaml -> "include"
            | `Sml -> "open"))
      ; (Indent, layout_module lang pincl_mod)
      ]
  | Pstr_attribute attribute ->
    layout_attributes ~depth:3 [attribute]
  | Pstr_eval _
  | Pstr_primitive _
  | Pstr_typext _
  | Pstr_exception _
  | Pstr_class _
  | Pstr_class_type _
  | Pstr_extension _
    ->
    raise_s [%message "unsupported structure item7"]

and layout_structure lang structure =
  list
    (List.map structure ~f:(fun structure_item ->
       (No_indent, layout_structure_item lang structure_item)))

and layout_open_decl
      lang
      ({ popen_expr; popen_override; popen_attributes = _; popen_loc = _ } : open_declaration)
  =
  match lang with
  | `Sml -> raise_s [%message "open is not supported in sml."]
  | `Ocaml ->
    let open_keyword =
      match popen_override with
      | Override -> "open!"
      | Fresh -> "open"
    in
    list [ (No_indent, atom open_keyword); (Indent, layout_module lang popen_expr) ]
;;
