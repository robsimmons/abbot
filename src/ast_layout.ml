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

let lparen = Layout.Atom_magnet_right "("
let rparen = Layout.Atom_magnet_left ")"
let comma = Layout.Atom_magnet_left ","

let rec layout_core_type
          ~outer_precedence
          ({ ptyp_desc; ptyp_attributes = _; ptyp_loc = _ } : core_type)
  : Layout.t =
  match ptyp_desc with
  | Ptyp_any -> Atom "_"
  | Ptyp_var name -> Atom ("'" ^ name)
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
    let (arrow_type : Layout.t) =
      List
        ((Layout.Indentation.No_indent,
          (match label with
           | Nolabel -> layout_core_type ~outer_precedence:`Arrow arg_type
           | Labelled label ->
             List
               [ (No_indent, Atom_magnet_right (label ^ ":"))
               ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
               ]
           | Optional label ->
             List
               [ (No_indent, Atom_magnet_right ("?" ^ label ^ ":"))
               ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
               ]))
         :: List.map other_arg_types ~f:(fun (label, arg_type) : (Layout.Indentation.t * Layout.t) ->
           (No_indent,
            List
              [ (No_indent, Atom "->")
              ; (No_indent,
                 (match label with
                  | Nolabel -> layout_core_type ~outer_precedence:`Arrow arg_type
                  | Labelled label ->
                    List
                      [ (No_indent, Atom_magnet_right (label ^ ":"))
                      ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
                      ]
                  | Optional label ->
                    List
                      [ (No_indent, Atom_magnet_right ("?" ^ label ^ ":"))
                      ; (Indent, layout_core_type ~outer_precedence:`Arrow arg_type)
                      ]))
              ]))
         @ [ (No_indent,
              List
                [ (No_indent, Atom "->")
                ; (No_indent, layout_core_type ~outer_precedence:`Arrow result_type)
                ])
           ])
    in
    (* CR wduff: There is probably a better way to deal with these parens. *)
    begin
      match add_parens with
      | false -> arrow_type
      | true -> List [ (No_indent, lparen); (Indent, arrow_type); (No_indent, rparen) ]
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
        let tuple_type = layout_tuple_type field fields in
        (* CR wduff: There is probably a better way to deal with these parens. *)
        match add_parens with
        | false -> tuple_type
        | true -> List [ (No_indent, lparen); (Indent, tuple_type); (No_indent, rparen) ]
    end
  | Ptyp_constr (constructor, args) ->
    begin
      match args with
      | [] -> Atom (string_of_lident constructor)
      | [arg] ->
        (* CR wduff: The indentation here is weird, but it isn't clear if there is a good option. *)
        List
          [ (Indent, layout_core_type ~outer_precedence:`Space arg)
          ; (No_indent, Atom (string_of_lident constructor)) ]
      | _::_::_ ->
        List
          (* CR wduff: There is probably a better way to deal with these parens and commas. *)
          (* CR wduff: Use layout_tuple. *)
          [ (Indent,
             List
               ((Layout.Indentation.No_indent, lparen)
                 :: List.intersperse ~sep:(No_indent, comma)
                      (List.map args ~f:(fun arg ->
                         (Layout.Indentation.Indent, layout_core_type ~outer_precedence:`None arg)))
                 @ [ (No_indent, rparen) ]))
          ; (No_indent, Atom (string_of_lident constructor))
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

and layout_tuple_type field fields : Layout.t =
  List
    ((No_indent, layout_core_type ~outer_precedence:`Star field)
     :: List.map fields ~f:(fun field ->
       (Layout.Indentation.No_indent,
        Layout.List
          [ (No_indent, Atom "*")
          ; (No_indent, layout_core_type ~outer_precedence:`Star field)
          ])))
;;

let layout_constant constant : Layout.t =
  match constant with
  | Pconst_integer (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        Atom string
    end
  | Pconst_char char ->
    Atom (sprintf "'%c'" char)
  | Pconst_string (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        Atom (sprintf "\"%s\"" string)
    end
  | Pconst_float (string, opt) ->
    begin
      match opt with
      | Some _ ->
        raise_s [%message "unsupported constant"]
      | None ->
        Atom string
    end
;;

let layout_attributes ~depth attributes : Layout.t =
  List
    (List.map attributes ~f:(fun (name, payload) : (Layout.Indentation.t * Layout.t) ->
       match payload with
       | PStr [ { pstr_desc = Pstr_eval ({ pexp_desc; pexp_attributes = []; pexp_loc = _ }, []); pstr_loc = _ } ] ->
         let (payload_layout : Layout.t) =
           match pexp_desc with
           | Pexp_ident lident -> Atom (string_of_lident lident)
           | Pexp_tuple exprs ->
             (* CR wduff: There is probably a better way to deal with these commas. *)
             List
               (List.intersperse ~sep:(No_indent, comma)
                  (List.map exprs ~f:(function
                     |  { pexp_desc = Pexp_ident lident; pexp_attributes = []; pexp_loc = _ } ->
                       (Layout.Indentation.Indent, Layout.Atom (string_of_lident lident))
                     | _ ->
                       raise_s [%message "unsupported attribute"])))
           | Pexp_constant constant ->
             layout_constant constant
           | _ -> raise_s [%message "unsupported attribute"]
         in
         (No_indent,
          List
            [ (No_indent, Atom ("[" ^ String.init depth ~f:(const '@') ^ name.txt))
            ; (Indent, payload_layout)
            ; (No_indent, Atom_magnet_left "]")
            ])
       | _ ->
         raise_s [%message "unsupported attribute"]))
;;

let layout_field_decl { pld_name; pld_mutable; pld_type; pld_attributes = _; pld_loc = _ } : Layout.t =
  List
    [ (No_indent,
       (match pld_mutable with
        | Immutable -> Atom pld_name.txt
        | Mutable -> List [ (No_indent, Atom "mutable"); (Indent, Atom pld_name.txt) ]))
    ; (Indent,
       List [ (No_indent, Atom ":"); (Indent, layout_core_type ~outer_precedence:`None pld_type) ])
    ]
;;

let layout_field_defn field_name value : Layout.t =
  List
    [ (No_indent, List [ (No_indent, Atom field_name); (No_indent, Atom "=") ])
    ; (Indent, value)
    ]
;;

let layout_record field fields : Layout.t =
  List
    (((Layout.Indentation.No_indent,
       Layout.List [ (No_indent, Atom "{"); (Indent, field) ]))
     :: List.map fields ~f:(fun field ->
       (* CR wduff: It's weird that we will put a space before the semi-colons. *)
       (Layout.Indentation.No_indent,
        Layout.List [ (No_indent, Atom ";"); (Indent, field) ]))
     @ [ (No_indent, Atom "}") ])
;;

let layout_field_decls field fields : Layout.t =
  layout_record (layout_field_decl field) (List.map fields ~f:layout_field_decl)
;;

let layout_constructor_args (constructor_args : constructor_arguments) : Layout.t option =
  match constructor_args with
  | Pcstr_tuple fields ->
    begin
      match fields with
      | [] -> None
      | field::fields ->
        Some (layout_tuple_type field fields)

    end
  | Pcstr_record fields ->
    begin
      match fields with
      | [] -> None
      | field::fields ->
        Some (layout_field_decls field fields)
    end
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
  : Layout.t =
  match (lang, ptype_manifest, ptype_kind) with
  | (`Sml, Some core_type, Ptype_variant _) ->
    begin
      match ptype_params with
      | _::_ ->
        raise_s [%message "Sml datatype redefinitions shouldn't have parameters."]
      | [] ->
        List
          [ (No_indent,
             List
               [ (No_indent, Atom start_keyword)
               ; (Indent, Atom ptype_name.txt)
               ; (No_indent, Atom "=")
               ])
          ; (Indent,
             List
               [ (No_indent, Atom "datatype")
               ; (Indent, layout_core_type ~outer_precedence:`None core_type)
               ])
          ]
    end
  | _ ->
    let (name_and_params : Layout.t) =
      match ptype_params with
      | [] -> Atom ptype_name.txt
      | _::_ ->
        List
          [ (Indent,
             List
               ((Layout.Indentation.No_indent, lparen)
                :: List.intersperse ~sep:(No_indent, comma)
                     (List.map ptype_params
                        ~f:(fun ({ ptyp_desc; ptyp_attributes = _; ptyp_loc = _ }, variance)
                                : (Layout.Indentation.t * Layout.t) ->
                             let variance_string =
                               match variance with
                               | Invariant -> ""
                               | Covariant -> "+"
                               | Contravariant -> "-"
                             in
                             (Indent,
                              match ptyp_desc with
                              | Ptyp_any -> Atom (variance_string ^ "_")
                              | Ptyp_var name -> Atom (variance_string ^ "'" ^ name)
                              | _ ->
                                raise_s [%message "unsupported type parameter"])))
                @ [ (No_indent, rparen) ]))
          ; (No_indent, Atom ptype_name.txt)
          ]
    in
    let (without_definition : (Layout.Indentation.t * Layout.t) list) =
      match ptype_manifest with
      | None -> [ (No_indent, Atom start_keyword); (Indent, name_and_params) ]
      | Some core_type ->
        [ (No_indent,
           List [ (No_indent, Atom start_keyword); (Indent, name_and_params); (No_indent, Atom "=") ])
        ; (Indent, layout_core_type ~outer_precedence:`None core_type)
        ]
    in
    let (without_attributes : Layout.t) =
      match ptype_kind with
      | Ptype_abstract -> List without_definition
      | Ptype_open -> List (without_definition @ [ (No_indent, Atom "="); (Indent, Atom "..") ])
      | Ptype_variant constructors ->
        List
          ((No_indent, List (without_definition @ [ (No_indent, Atom "=") ]))
           ::
           (* CR wduff: We need a way to specify that the first '|' should be dropped if the lines
              are not split.

              Alternatively, we could just force a split, but either way the feature to support the
              first idea seems like a good one to have. *)
           (List.mapi constructors
              ~f:(fun i { pcd_name; pcd_args; pcd_res; pcd_attributes = _; pcd_loc = _ } ->
                let (start : Layout.t) =
                  match lang with
                  | `Ocaml ->
                    List [ (No_indent, Atom "|"); (Indent, Atom pcd_name.txt) ]
                  | `Sml ->
                    match i with
                    | 0 -> List [ (Indent, Atom pcd_name.txt) ]
                    | _ ->
                      List [ (No_indent, Atom "|"); (Indent, Atom pcd_name.txt) ]
                in
                (Layout.Indentation.Indent,
                 match layout_constructor_args pcd_args with
                 | None ->
                   begin
                     match pcd_res with
                     | None -> start
                     | Some res_type ->
                       List
                         [ (No_indent, start)
                         ; (Indent,
                            List
                              [ (No_indent, Atom ":")
                              ; (Indent, layout_core_type ~outer_precedence:`None res_type)
                              ])
                         ]
                   end
                 | Some constructor_args ->
                   begin
                     match pcd_res with
                     | None ->
                       List
                         [ (No_indent, start)
                         ; (Indent, List [ (No_indent, Atom "of"); (Indent, constructor_args) ])
                         ]
                     | Some res_type ->
                       List
                         [ (No_indent, start)
                         ; (Indent,
                            List
                              [ (No_indent, Atom ":")
                              ; (Indent,
                                 List
                                   [ (No_indent, constructor_args)
                                   ; (No_indent,
                                      List
                                        [ (No_indent, Atom "->")
                                        ; (No_indent,
                                           layout_core_type ~outer_precedence:`None res_type)
                                        ])
                                   ])
                              ])
                         ]
                   end))))
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
      List
        [ (No_indent, without_attributes)
        ; (No_indent, layout_attributes ~depth:2 ptype_attributes)
        ]
;;

let layout_type_decls' lang ~first_start_keyword type_decls
  : (Layout.Indentation.t * Layout.t) list =
  match type_decls with
  | [] -> []
  | decl :: decls ->
    (* CR wduff: Maybe in some cases, such as this one,
       we should force a newline between the items. *)
    (No_indent, layout_type_decl lang ~start_keyword:first_start_keyword decl)
    :: List.map decls ~f:(fun decl ->
      (Layout.Indentation.No_indent, layout_type_decl lang ~start_keyword:"and" decl))
;;

let layout_type_decls lang rec_flag type_decls : Layout.t =
  match lang with
  | `Ocaml ->
    let first_start_keyword =
      match rec_flag with
      | Recursive -> "type"
      | Nonrecursive -> "type nonrec"
    in
    List (layout_type_decls' lang ~first_start_keyword type_decls)
  | `Sml ->
    let (datatype_decls, type_alias_decls) =
      List.partition_tf type_decls ~f:(fun type_decl ->
        match type_decl.ptype_kind with
        | Ptype_variant _ -> true
        | _ -> false)
    in
    match datatype_decls with
    | [] ->
      List (layout_type_decls' lang ~first_start_keyword:"type" type_alias_decls)
    | _::_ ->
      List
        (layout_type_decls' lang ~first_start_keyword:"datatype" datatype_decls
         @ layout_type_decls' lang ~first_start_keyword:"withtype" type_alias_decls)
;;

let layout_open
      lang
      ({ popen_lid; popen_override; popen_attributes = _; popen_loc = _ } : open_description)
  : Layout.t =
  match lang with
  | `Sml -> raise_s [%message "open is not supported in sml."]
  | `Ocaml ->
    let open_keyword =
      match popen_override with
      | Override -> "open!"
      | Fresh -> "open"
    in
    List [ (No_indent, Atom open_keyword); (Indent, Atom (string_of_lident popen_lid)) ]
;;

let rec layout_module_type lang ({ pmty_desc; pmty_attributes = _; pmty_loc = _ } : module_type) : Layout.t =
  match pmty_desc with
  | Pmty_ident lident -> Atom (string_of_lident lident)
  | Pmty_signature signature ->
    List [ (No_indent, Atom "sig"); (Indent, layout_signature lang signature); (No_indent, Atom "end") ]
  | Pmty_functor (arg_name, arg_type, result_type) ->
    (* Should we lift "sig" here as well? Is there some generic way to lift it everywhere? *)
    (* CR wduff: Consider flattening if the arg name is unused in the result. *)
    List
      [ (No_indent,
         List
           [ (No_indent, Atom "functor")
           ; (Indent, layout_module_arg lang arg_name arg_type)
           ; (No_indent, Atom "->")
           ])
      ; (Indent, layout_module_type lang result_type)
      ]
  | Pmty_with (module_type, with_constraints) ->
    List
      ((No_indent, layout_module_type lang module_type)
       :: List.map with_constraints ~f:(fun with_constraint : (Layout.Indentation.t * Layout.t) ->
         (* CR wduff: Handle params in the type cases, and check that weird stuff doesn't show up in
            the type declarations. *)
         (Indent,
          match with_constraint with
          | Pwith_type (lident, type_decl) ->
            List
              [ (No_indent,
                 List
                   [ (No_indent, Atom (with_type_keyword lang))
                   ; (Indent,
                      (match type_decl.ptype_params with
                       | [] -> Atom (string_of_lident lident)
                       | _::_ ->
                         List
                           [ (Indent,
                              List
                                [ (No_indent, lparen)
                                ; (Indent,
                                   List
                                     (List.map type_decl.ptype_params ~f:(fun (param, _variance) ->
                                        (Layout.Indentation.No_indent,
                                         layout_core_type ~outer_precedence:`None param))
                                      |> List.intersperse ~sep:(No_indent, comma)))
                                ; (No_indent, rparen)
                                ])
                           ; (No_indent, Atom (string_of_lident lident))
                           ]))
                   ; (No_indent, Atom "=")
                   ])
              ; (Indent,
                 layout_core_type
                   ~outer_precedence:`None
                   (Option.value_exn type_decl.ptype_manifest))
              ]
          | Pwith_module (lident1, lident2) ->
            List
              [ (No_indent,
                 List
                   [ (No_indent, Atom (with_module_keyword lang))
                   ; (Indent, Atom (string_of_lident lident1))
                   ; (No_indent, Atom "=")
                   ])
              ; (Indent, Atom (string_of_lident lident2))
              ]
          | Pwith_typesubst (lident, type_decl) ->
            List
              [ (No_indent,
                 List
                   [ (No_indent, Atom (with_type_keyword lang))
                   ; (Indent,
                      (match type_decl.ptype_params with
                       | [] -> Atom (string_of_lident lident)
                       | _::_ ->
                         List
                           [ (Indent,
                              List
                                [ (No_indent, lparen)
                                ; (Indent,
                                   List
                                     (List.map type_decl.ptype_params ~f:(fun (param, _variance) ->
                                        (Layout.Indentation.No_indent,
                                         layout_core_type ~outer_precedence:`None param))
                                      |> List.intersperse ~sep:(No_indent, comma)))
                                ; (No_indent, rparen)
                                ])
                           ; (No_indent, Atom (string_of_lident lident))
                           ]))
                   ; (No_indent, Atom ":=")
                   ])
              ; (Indent,
                 layout_core_type
                   ~outer_precedence:`None
                   (Option.value_exn type_decl.ptype_manifest))
              ]
          | Pwith_modsubst (lident1, lident2) ->
            List
              [ (No_indent,
                 List
                   [ (No_indent, Atom (with_module_keyword lang))
                   ; (Indent, Atom (string_of_lident lident1))
                   ; (No_indent, Atom ":=")
                   ])
              ; (Indent, Atom (string_of_lident lident2))
              ])))
  | Pmty_alias _ | Pmty_typeof _ | Pmty_extension _ ->
    raise_s [%message "unsupported module type"]

and layout_module_type_decl lang { pmtd_name; pmtd_type; pmtd_attributes = _; pmtd_loc = _ }
  : Layout.t =
  (* CR wduff: Special case sig ... end. *)
  match pmtd_type with
  | None -> List [ (No_indent, Atom (module_type_keyword lang)); (Indent, Atom pmtd_name.txt) ]
  | Some module_type ->
    List
      [ (No_indent,
         List
           [ (No_indent, Atom (module_type_keyword lang))
           ; (Indent, Atom pmtd_name.txt)
           ; (No_indent, Atom "=")
           ])
      ; (Indent, layout_module_type lang module_type)
      ]

and layout_module_arg lang arg_name arg_type : Layout.t =
  match arg_type with
  | None -> List [ (No_indent, lparen); (Indent, Atom arg_name.txt); (No_indent, rparen) ]
  | Some arg_type ->
    List
      [ (No_indent, List [ (No_indent, lparen); (Indent, Atom arg_name.txt) ])
      (* CR wduff: The rparen should maybe go on the next line unless we are going to tightly couple
         it to the last token. *)
      ; (Indent,
         List [ (No_indent, Atom ":"); (Indent, layout_module_type lang arg_type); (No_indent, rparen) ])
      ]

and layout_module_decl lang ~start_keyword { pmd_name; pmd_type; pmd_attributes = _; pmd_loc = _ } : Layout.t =
  let rec strip_functor_args (({ pmty_desc; pmty_attributes = _; pmty_loc = _ } as module_type) : module_type) =
    match pmty_desc with
    | Pmty_functor (arg_name, arg_type, result_type) ->
      let (args, result_type) = strip_functor_args result_type in
      ((Layout.Indentation.Indent, layout_module_arg lang arg_name arg_type) :: args, result_type)
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
  let (start : (Layout.Indentation.t * Layout.t) list) =
    (No_indent, List [ (No_indent, Atom start_keyword); (Indent, Atom pmd_name.txt) ]) :: args
  in
  (* CR wduff: Shouldn't the colon by default be on the next line? *)
  match result_type.pmty_desc with
  | Pmty_signature signature ->
    List
      [ (No_indent, List (start @ [ (No_indent, Atom ":"); (No_indent, Atom "sig") ]))
      ; (Indent, layout_signature lang signature)
      ; (No_indent, Atom "end")
      ]
  | Pmty_alias lident ->
    List
      [ (No_indent, List (start @ [ (No_indent, Atom "=") ]))
      ; (Indent, Atom (string_of_lident lident))
      ]
  | _ ->
    List
      [ (No_indent, List start)
      ; (Indent, List [ (No_indent, Atom ":"); (Indent, layout_module_type lang result_type) ])
      ]

and layout_signature_item lang ({ psig_desc; psig_loc = _ } : signature_item) : Layout.t =
  match psig_desc with
  | Psig_value { pval_name; pval_type; pval_prim; pval_attributes = _; pval_loc = _ } ->
    begin
      match pval_prim with
      | [] -> ()
      | _::_ -> raise_s [%message "unsupported signature item"]
    end;
    List
      [ (No_indent, List [ (No_indent, Atom "val"); (Indent, Atom pval_name.txt) ])
      ; (Indent,
         List
           [ (No_indent, Atom ":"); (Indent, layout_core_type ~outer_precedence:`None pval_type) ])
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
          (* CR wduff: Better error. *)
          raise_s [%message "wtf"]
        | decl :: decls ->
          List
            ((No_indent, layout_module_decl lang ~start_keyword:"module rec" decl)
             :: List.map decls ~f:(fun decl ->
               (Layout.Indentation.No_indent, layout_module_decl lang ~start_keyword:"and" decl)))
    end
  | Psig_modtype module_type_decl ->
    layout_module_type_decl lang module_type_decl
  | Psig_open open_description ->
    layout_open lang open_description
  | Psig_include { pincl_mod; pincl_attributes = _; pincl_loc = _ } ->
    List [ (No_indent, Atom "include"); (Indent, layout_module_type lang pincl_mod) ]
  | Psig_extension (extension, _) ->
    begin
      match extension with
      | ({ txt = "sharing_type"; loc = _ },
         PTyp { ptyp_desc = Ptyp_tuple [ type1; type2 ]; ptyp_attributes = _; ptyp_loc = _ })
        ->
        List
          [ (No_indent, Atom "sharing type")
          ; (Indent,
             List
               [ (No_indent, layout_core_type ~outer_precedence:`None type1)
               ; (No_indent, Atom "=")
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
    ->
    raise_s [%message "unsupported signature item"]

and layout_signature lang signature : Layout.t =
  List
    (List.map signature ~f:(fun signature_item ->
       (Layout.Indentation.No_indent, layout_signature_item lang signature_item)))
;;

let layout_arg arg_label arg : Layout.t =
  match arg_label with
  | Nolabel -> arg
  | Labelled label ->
    List [ (No_indent, Atom ("~" ^ label ^ ":")); (Indent, arg) ]
  | Optional label ->
    List [ (No_indent, Atom ("?" ^ label ^ ":")); (Indent, arg) ]
;;

let layout_tuple fields : Layout.t =
  List
    ((Layout.Indentation.No_indent, lparen)
     :: List.intersperse ~sep:(No_indent, comma)
          (List.map fields ~f:(fun field ->
             (Layout.Indentation.Indent, field)))
     @ [ (No_indent, rparen) ])
;;

let rec layout_pattern lang ~outer_precedence { ppat_desc; ppat_attributes = _; ppat_loc = _ } : Layout.t =
  match ppat_desc with
  | Ppat_any -> Atom "_"
  | Ppat_var name -> Atom name.txt
  | Ppat_alias (pat, alias) ->
    List
      [ (No_indent, layout_pattern lang ~outer_precedence:`As pat)
      ; (No_indent, List [ (No_indent, Atom "as"); (No_indent, Atom alias.txt) ])
      ]
  | Ppat_constant constant -> layout_constant constant
  | Ppat_interval (constant1, constant2) ->
    List
      [ (No_indent, layout_constant constant1)
      ; (No_indent, List [ (No_indent, Atom ".."); (No_indent, layout_constant constant2) ])
      ]
  | Ppat_tuple pats ->
    layout_tuple (List.map pats ~f:(layout_pattern ~outer_precedence:`Tuple_elt lang))
  | Ppat_construct (constructor, pat_opt) ->
    begin
      match pat_opt with
      | None -> Atom (string_of_lident constructor)
      | Some pat ->
        let include_parens =
          match outer_precedence with
          | `None | `As | `Or | `Constrained | `Record_elt | `Tuple_elt -> false
          | `Force_parens | `Fun_arg | `Constr_arg -> true
        in
        List
          [ (No_indent,
             List
               ((match include_parens with
                  | false -> []
                  | true -> [ (Layout.Indentation.No_indent, lparen) ])
                @
               [ (Layout.Indentation.Indent, Atom (string_of_lident constructor)) ]))
          ; (Indent,
             List
               ([ (Layout.Indentation.No_indent, layout_pattern lang ~outer_precedence:`Constr_arg pat) ]
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
          | Open -> [ Atom "_" ])
      with
      | [] ->
        (* CR wduff: Better error. *)
        raise_s [%message "wtf"]
      | field :: fields ->
        layout_record field fields
    end
  | Ppat_or (pat1, pat2) ->
    (* CR wduff: This surely needs parens sometimes. *)
    List
      [ (No_indent, layout_pattern lang ~outer_precedence:`Or pat1)
      ; (No_indent,
         List
           [ (No_indent, Atom "|")
           ; (Indent, layout_pattern lang ~outer_precedence:`Or pat2)
           ])
      ]
  | Ppat_constraint (pat, core_type) ->
    (* CR wduff: Reduce duplication. *)
    List
      [ (No_indent,
         List
           [ (No_indent, lparen)
           ; (Indent, layout_pattern lang ~outer_precedence:`Constrained pat)
           ])
      ; (Indent,
         List
           [ (No_indent, Atom ":")
           ; (Indent, layout_core_type ~outer_precedence:`None core_type)
           ; (No_indent, rparen)
           ])
      ]
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

(* CR wduff: Are the precedence rules right for sml? *)
(* CR wduff: Fix the way parens work here. Remove superfluous ones, add needed ones, and maybe use
   begin ... end for multi line stuff in the ocaml case. *)
let rec layout_expression lang ~outer_precedence { pexp_desc; pexp_attributes = _; pexp_loc = _ } : Layout.t =
  match pexp_desc with
  | Pexp_ident lident -> Atom (string_of_lident lident)
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
          | `List_elt
          | `Record_elt
          | `Tuple_elt
          | `Infix_arg
          | `Fun
          | `Fun_arg
            ->
            true
        in
        let (value_binding_indentation : Layout.Indentation.t) =
          match lang with
          | `Ocaml -> No_indent
          | `Sml -> Indent
        in
        List
          ([ (No_indent,
              List
                ((match (lang, include_parens) with
                   | (`Ocaml, false) -> []
                   | (`Ocaml, true) -> [ (Layout.Indentation.No_indent, lparen) ]
                   | (`Sml, false) -> [ (Layout.Indentation.No_indent, Layout.Atom "let") ]
                   | (`Sml, true) -> [ (Layout.Indentation.No_indent, Layout.Atom "(let") ])
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
                 [ (No_indent, Atom "in") ]))
           ; (No_indent,
              List
                ([ (Layout.Indentation.No_indent,
                    layout_expression lang ~outer_precedence:`Let_body body) ]
                 @
                 (match (lang, include_parens) with
                    | (`Ocaml, false) -> []
                    | (`Ocaml, true) -> [ (Layout.Indentation.No_indent, rparen) ]
                    | (`Sml, false) -> [ (No_indent, Atom "end") ]
                    | (`Sml, true) -> [ (No_indent, Atom "end)") ])))
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
          | `List_elt
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
        List
          ((No_indent, Atom "function")
           :: List.mapi cases ~f:(fun i case : (Layout.Indentation.t * Layout.t) ->
             (No_indent, layout_match_case lang ~first_case:(Int.equal i 0) case)))
    end
  | Pexp_fun (arg_label, default_opt, arg_pat, body) ->
    begin
      match default_opt with
      | Some _ ->
        raise_s [%message "unsupported expression"]
      | None ->
        (* CR wduff: Drop parens sometimes? Maybe if it is the entire expression or something? *)
        List
          [ (No_indent,
             List
               [ (No_indent,
                  Atom
                    (match lang with
                     | `Ocaml -> "(fun"
                     | `Sml -> "(fn"))
               ; (Indent,
                  layout_arg arg_label (layout_pattern lang ~outer_precedence:`Fun_arg arg_pat))
               ; (No_indent,
                  Atom
                    (match lang with
                     | `Ocaml -> "->"
                     | `Sml -> "=>"))
               ])
          ; (Indent, layout_expression lang ~outer_precedence:`Fun_body body)
          ; (No_indent, rparen)
          ]
    end
  | Pexp_newtype (type_name, body) ->
    begin
      match lang with
      | `Sml -> raise_s [%message "unsupported expression in sml"]
      | `Ocaml ->
        (* CR wduff: Drop parens sometimes? Maybe if it is the entire expression or something? *)
        List
          [ (No_indent,
             List
               [ (No_indent, Atom "(fun")
               ; (Indent, Atom (sprintf "(type %s)" type_name.txt))
               ; (No_indent, Atom "->")
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
          | `List_elt
          | `Record_elt
          | `Tuple_elt
          | `Infix_arg
            ->
            false
          | `Force_parens | `Fun | `Fun_arg ->
            true
        in
        List
          ((match include_parens with
             | false ->  []
             | true -> [ (Layout.Indentation.No_indent, lparen) ])
           @
           [ (Layout.Indentation.No_indent, layout_expression lang ~outer_precedence:`Fun func) ]
           @
           List.map args ~f:(fun (arg_label, arg) : (Layout.Indentation.t * Layout.t) ->
             (Indent, layout_arg arg_label (layout_expression lang ~outer_precedence:`Fun_arg arg)))
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
              | `List_elt
              | `Record_elt
              | `Tuple_elt
                ->
                false
              | `Force_parens | `Infix_arg | `Fun | `Fun_arg ->
                true
            in
            List
              ((match include_parens with
                 | false -> []
                 | true -> [ (Layout.Indentation.No_indent, lparen) ])
               @
               [ (Layout.Indentation.No_indent,
                   layout_arg arg_label (layout_expression lang ~outer_precedence:`Infix_arg arg))
               ; (No_indent, Atom oper)
               ]
               @
               List.map args ~f:(fun (arg_label, arg) : (Layout.Indentation.t * Layout.t) ->
                 (Indent,
                  layout_arg arg_label (layout_expression lang ~outer_precedence:`Infix_arg arg)))
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
      | `List_elt
      | `Record_elt
      | `Tuple_elt
      | `Force_parens
      | `Infix_arg
      | `Fun
      | `Fun_arg
        ->
        true
    in
    List
      ((Layout.Indentation.No_indent,
        Layout.List
          [ (No_indent,
             Atom
               (match (lang, include_parens) with
                | (`Ocaml, false) -> "match"
                | (`Ocaml, true) -> "(match"
                | (`Sml, false) -> "case"
                | (`Sml, true) -> "(case"))
          ; (Indent, layout_expression lang ~outer_precedence:`Match expr)
          ; (No_indent,
             Atom
               (match lang with
                | `Ocaml -> "with"
                | `Sml -> "of"))
          ])
       :: List.mapi cases ~f:(fun i case : (Layout.Indentation.t * Layout.t) ->
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
      | None -> Atom constructor
      | Some arg ->
        match constructor with
        | "::" ->
          begin
            match try_to_get_list_elements arg with
            | Some (elt, elts) ->
              List
                ([ (Layout.Indentation.No_indent,
                    Layout.List
                      [ (No_indent, Atom "[")
                      ; (Indent, layout_expression lang ~outer_precedence:`List_elt elt)
                      ])
                 ]
                 @
                 List.map elts ~f:(fun elt ->
                   (Layout.Indentation.No_indent,
                    (* CR wduff: This needs to be a "," in sml. *)
                    Layout.List
                      [ (No_indent, Atom ";")
                      ; (Indent, layout_expression lang ~outer_precedence:`List_elt elt)
                      ]))
                 @
                 [ (Layout.Indentation.No_indent, Layout.Atom "]") ])
            | None ->
              match arg.pexp_desc with
              | Pexp_tuple [ head; tail ] ->
                List
                  [ (No_indent, layout_expression lang ~outer_precedence:`Infix_arg head)
                  ; (No_indent,
                     List
                       [ (No_indent, Atom "::")
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
            | `List_elt
            | `Record_elt
            | `Tuple_elt
            | `Infix_arg
              ->
              false
            | `Force_parens | `Fun | `Fun_arg ->
              true
          in
          List
            ((match include_parens with
                | false -> []
                | true -> [ (Layout.Indentation.No_indent, lparen) ])
             @
             [ (Layout.Indentation.No_indent, Layout.Atom constructor)
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
          (* CR wduff: Better error. *)
          raise_s [%message "wtf"]
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
      | `List_elt
      | `Record_elt
      | `Tuple_elt
      | `Infix_arg
      | `Fun
      | `Fun_arg ->
        true
    in
    List
      ((match include_parens with
         | false -> []
         | true -> [ (Layout.Indentation.No_indent, lparen) ])
       @
       [ (Layout.Indentation.No_indent,
          Layout.List
            [ (No_indent, layout_expression lang ~outer_precedence:`Sequence_elt expr1)
            ; (No_indent, Atom_magnet_left ";")
            ])
       ; (No_indent, layout_expression lang ~outer_precedence:`Sequence_elt expr2)
       ]
       @
       (match include_parens with
         | false -> []
         | true -> [ (No_indent, rparen) ]))
  | Pexp_constraint (expr, core_type) ->
    (* CR wduff: Reduce duplication. *)
    List
      [ (No_indent,
         List
           [ (No_indent, lparen)
           ; (Indent, layout_expression lang ~outer_precedence:`Constrained expr)
           ])
      ; (Indent,
         List
           [ (No_indent, Atom ":")
           ; (Indent, layout_core_type ~outer_precedence:`None core_type)
           ; (No_indent, rparen)
           ])
      ]
  | Pexp_extension extension ->
    layout_extension lang ~depth:1 extension
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
  | Pexp_letmodule _
  | Pexp_letexception _
  | Pexp_assert _
  | Pexp_lazy _
  | Pexp_poly _
  | Pexp_object _
  | Pexp_pack _
  | Pexp_open _
  | Pexp_unreachable
    ->
    raise_s [%message "unsupported expression"]

and layout_value_binding
      lang
      (rec_flag : rec_flag)
      ~is_first_in_group
      { pvb_pat; pvb_expr; pvb_attributes = _; pvb_loc = _ }
  : Layout.t =
  let rec strip_function_args (({ pexp_desc; pexp_attributes = _; pexp_loc = _ } as expr) : expression) =
    match pexp_desc with
    | Pexp_fun (arg_label, default_opt, arg_pat, body) ->
      begin
        match default_opt with
        | Some _ ->
          raise_s [%message "unsupported expression"]
        | None ->
          let (args, body) = strip_function_args body in
          (layout_arg arg_label (layout_pattern lang ~outer_precedence:`Fun_arg arg_pat) :: args,
           body)
      end
    | _ -> ([], expr)
  in
  let (args, body) =
    match pvb_pat.ppat_desc with
    | Ppat_var _ -> strip_function_args pvb_expr
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
  List
     [ (No_indent,
        List
          [ (No_indent,
             List
               ((No_indent,
                 List
                   [ (No_indent, Atom start_keyword)
                   ; (Indent, layout_pattern lang ~outer_precedence:`None pvb_pat)
                   ])
               ::
               List.map args ~f:(fun arg ->
                 (Layout.Indentation.Indent, Layout.List [ (Indent, arg)]))))
          ; (Indent,
             (match result_type with
              | None -> Atom "="
              | Some result_type ->
                List
                  [ (No_indent, Atom ":")
                  ; (Indent, layout_core_type ~outer_precedence:`None result_type)
                  ; (No_indent, Atom "=")
                  ]))
          ])
       ; (Indent, layout_expression lang ~outer_precedence:`None body)
     ]

and layout_extension lang ~depth (name, payload) =
  let (include_colon, payload_layout) =
    match payload with
    | PStr [ { pstr_desc = Pstr_eval (expr, []); pstr_loc = _ } ] ->
      (false, layout_expression lang ~outer_precedence:`None expr)
    | PTyp core_type ->
      (true, layout_core_type ~outer_precedence:`None core_type)
    | _ ->
      raise_s [%message "unsupported extension point"]
  in
  List
    [ (No_indent,
       Atom
         ("["
          ^ String.init depth ~f:(const '%')
          ^ name.txt
          ^ (match include_colon with true -> ":" | false -> "")))
    ; (Indent, payload_layout)
    ; (No_indent, Atom_magnet_left "]")
    ]

and layout_match_case
      lang
      ~first_case
      { pc_lhs; pc_guard; pc_rhs }
  : Layout.t =
  match pc_guard with
  | Some _ ->
    raise_s [%message "unsupported match case"]
  | None ->
    match (lang, first_case) with
    | (`Sml, true) ->
      List
        [ (No_indent,
           List
             [ (Indent, layout_pattern lang ~outer_precedence:`None pc_lhs)
             ; (No_indent,
                Atom
                  (match lang with
                   | `Ocaml -> "->"
                   | `Sml -> "=>"))
             ])
        ; (Indent, layout_expression lang ~outer_precedence:`Case_rhs pc_rhs)
        ]
    | (`Sml, false) | (`Ocaml, _) ->
      (* CR wduff: Deal with or-patterns specially? *)
      List
        [ (No_indent,
           List
             [ (No_indent, Atom "|")
             ; (Indent, layout_pattern lang ~outer_precedence:`None pc_lhs)
             ; (No_indent,
                Atom
                  (match lang with
                   | `Ocaml -> "->"
                   | `Sml -> "=>"))
             ])
        ; (Indent, layout_expression lang ~outer_precedence:`Case_rhs pc_rhs)
        ]
;;

let rec layout_module lang { pmod_desc; pmod_attributes = _; pmod_loc = _ } : Layout.t =
  match pmod_desc with
  | Pmod_ident lident ->
    Atom (string_of_lident lident)
  | Pmod_structure structure ->
    List
      [ (No_indent, Atom "struct")
      ; (Indent, layout_structure lang structure)
      ; (No_indent, Atom "end")
      ]
  | Pmod_apply (module_expr1, module_expr2) ->
    List
      [ (No_indent, layout_module lang module_expr1)
      ; (Indent,
         List
           [ (No_indent, lparen)
           ; (Indent, layout_module lang module_expr2)
           ; (No_indent, rparen)
           ])
      ]
  | Pmod_constraint (module_expr, module_type) ->
    (* CR wduff: This logic is duplicated a lot. *)
    List
      [ (No_indent, List [ (No_indent, lparen); (Indent, layout_module lang module_expr) ])
      ; (Indent,
         List
           [ (No_indent, Atom (match lang with `Ocaml -> ":" | `Sml -> ":>"))
           ; (Indent, layout_module_type lang module_type)
           ; (No_indent, rparen)
           ])
      ]
  | Pmod_functor _
  | Pmod_unpack _
  | Pmod_extension _
    ->
    raise_s [%message "unsupported module"]

and layout_module_binding
      lang
      ~start_keyword
      { pmb_name; pmb_expr; pmb_attributes = _; pmb_loc = _ }
  : Layout.t =
  (* CR wduff: This code is largely a duplicate of layout_module_decl. *)
  let rec strip_functor_args (({ pmod_desc; pmod_attributes = _; pmod_loc = _ } as module_expr) : module_expr) =
    match pmod_desc with
    | Pmod_functor (arg_name, arg_type, body) ->
      let (args, body) = strip_functor_args body in
      ((Layout.Indentation.Indent, layout_module_arg lang arg_name arg_type) :: args, body)
    | _ -> ([], module_expr)
  in
  let (args, body) = strip_functor_args pmb_expr in
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
  let (start : (Layout.Indentation.t * Layout.t) list) =
    (No_indent, List [ (No_indent, Atom start_keyword); (Indent, Atom pmb_name.txt) ]) :: args
  in
  let ((start : (Layout.Indentation.t * Layout.t) list), body) =
    match body.pmod_desc with
    | Pmod_constraint (module_expr, module_type) ->
      ([ (No_indent, List (start @ [ (No_indent, Atom (match lang with `Ocaml -> ":" | `Sml -> ":>")) ]))
       ; (Indent, layout_module_type lang module_type)
       ; (No_indent, Atom "=")
       ],
       module_expr)
    | _ ->
      (start @ [ (No_indent, Atom "=") ], body)
  in
  match body.pmod_desc with
  | Pmod_structure structure ->
    List
      [ (No_indent, List (start @ [ (No_indent, Atom "struct") ]))
      ; (Indent, layout_structure lang structure)
      ; (No_indent, Atom "end")
      ]
  | _ ->
    List
      [ (No_indent, List start)
      ; (Indent, layout_module lang body)
      ]

and layout_structure_item lang ({ pstr_desc; pstr_loc = _ } : structure_item) : Layout.t =
  match pstr_desc with
  | Pstr_value (rec_flag, value_bindings) ->
    (* CR wduff: The structure of this code can probably be shared with other code. *)
    begin
      match value_bindings with
      | [] ->
        (* CR wduff: Better error. *)
        raise_s [%message "wtf"]
      | binding :: bindings ->
        List
          ((No_indent, layout_value_binding lang rec_flag ~is_first_in_group:true binding)
           :: List.map bindings ~f:(fun binding ->
             (Layout.Indentation.No_indent,
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
          List
            ((No_indent, layout_module_binding lang ~start_keyword:"module rec" binding)
             :: List.map bindings ~f:(fun binding ->
               (Layout.Indentation.No_indent,
                layout_module_binding lang ~start_keyword:"and" binding)))
    end
  | Pstr_modtype module_type_decl ->
    layout_module_type_decl lang module_type_decl
  | Pstr_open open_description ->
    layout_open lang open_description
  | Pstr_include { pincl_mod; pincl_attributes = _; pincl_loc = _ } ->
    List
      [ (No_indent,
         Atom
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

and layout_structure lang structure : Layout.t =
  List
    (List.map structure ~f:(fun structure_item ->
       (Layout.Indentation.No_indent, layout_structure_item lang structure_item)))
;;
