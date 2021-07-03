open! Core
open Ppxlib
open Ast_helper
open Typed
open Ast_gen_shared

let loc = Location.none

let keywords =
  String.Set.of_list
    [ "and"
    ; "as"
    ; "assert"
    ; "begin"
    ; "class"
    ; "constraint"
    ; "do"
    ; "done"
    ; "downto"
    ; "else"
    ; "end"
    ; "exception"
    ; "external"
    ; "false"
    ; "for"
    ; "fun"
    ; "function"
    ; "functor"
    ; "if"
    ; "in"
    ; "include"
    ; "inherit"
    ; "initializer"
    ; "lazy"
    ; "let"
    ; "match"
    ; "method"
    ; "module"
    ; "mutable"
    ; "new"
    ; "object"
    ; "of"
    ; "open"
    ; "or"
    ; "private"
    ; "rec"
    ; "sig"
    ; "struct"
    ; "then"
    ; "to"
    ; "true"
    ; "try"
    ; "type"
    ; "val"
    ; "virtual"
    ; "when"
    ; "while"
    ; "with"
    ]
;;

let subst_function_signature_item ~args =
  let t_with_args = Typ.constr (lident "t") (List.map args ~f:Typ.var) in
  [%sigi:
    val subst
      : [%t
        List.fold_right args
          ~init:[%type: ('var, 'sort) Sort.t -> 'sort -> 'var -> [%t t_with_args] -> [%t t_with_args]]
          ~f:(fun arg acc ->
            [%type:
              (('var, 'sort) Sort.t -> 'sort -> 'var -> [%t Typ.var arg] -> [%t Typ.var arg])
              -> [%t acc]])]]
;;

let shared_signature_items_of_defn ~current_name defn =
  let refer_to_via_module = const true in
  match defn with
  | `Simple_abt (args, cases) ->
    [ Sig.type_ Recursive
        [ Type.mk
            (ident "t")
            ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
            ~kind:
              (Ptype_variant
                 (List.map cases ~f:(fun (constructor_name, abt) ->
                    Type.constructor
                      (ident constructor_name)
                      ~args:
                        (Pcstr_tuple
                           (Option.to_list
                              (Option.map abt
                                 ~f:(exposed_type_of_abt
                                       ~use_temp_directly:false
                                       ~refer_to_via_module)))))))
            ~attrs:[deriving_sexp_attribute]
        ]
    ; subst_function_signature_item ~args
    ]
  | `Open_abt cases ->
    [ Sig.type_ Recursive
        [ type_decl_of_cases
            ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
            ~deriving_sexp:true
            ~name:"t"
            cases
        ]
    ; subst_function_signature_item ~args:[]
    ]
  | `Closed_abt cases ->
    [ Sig.type_ Recursive
        [ type_decl_of_cases
            ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
            ~deriving_sexp:true
            ~name:"view"
            cases
        ]
    ]
    @
    convenient_constructors_intf
      ~keywords
      ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
      ~is_sort:false
      cases
    @
    view_conversion_intf
    @
    [ subst_function_signature_item ~args:[] ]
  | `Sort cases ->
    [ Sig.type_ Recursive
        [ type_decl_of_cases
            ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
            ~extra_cases:
              [ Type.constructor
                  (ident "Var")
                  ~args:
                    (Pcstr_tuple
                       [ type_var ~via_module:true current_name ])
              ]
            ~deriving_sexp:true
            ~name:"view"
            cases
        ]
    ]
    @
    convenient_constructors_intf
      ~keywords
      ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
      ~is_sort:true
      cases
    @
    view_conversion_intf
    @
    [ subst_function_signature_item ~args:[]]
;;

let sort_type defns =
  [ Type.mk
      (ident "t")
      ~params:[ (Typ.any (), Invariant); (Typ.any (), Invariant) ]
      ~kind:
        (Ptype_variant
           (List.filter_map defns ~f:(fun (name, defn) ->
              match defn with
              | `Symbol ->
                Some
                  (Type.constructor
                     (ident (String.capitalize name))
                     ~res:
                       (Typ.constr (lident "t")
                          [ type_t ~via_module:true name
                          ; type_t ~via_module:true name
                          ]))
              | `Sort _ ->
                Some
                  (Type.constructor
                     (ident (String.capitalize name))
                     ~res:
                       (Typ.constr (lident "t")
                          [ type_var ~via_module:true name
                          ; type_t ~via_module:true name
                          ]))
              | _ -> None)))
  ]
;;

let sort_same_witness_cases defns =
  List.filter_map defns ~f:(fun (name, defn) ->
    match defn with
    | `Symbol | `Sort _ ->
      let constr = lident (String.capitalize name) in
      Some
        { pc_lhs = [%pat? ([%p Pat.construct constr None], [%p Pat.construct constr None])]
        ; pc_guard = None
        ; pc_rhs = [%expr Some (T, T)]
        }
    | _ -> None)
;;

let to_sort_or_symbol_eq_cases defns =
  (List.filter_map defns ~f:(fun (name, defn) ->
     match defn with
     | `Symbol | `Sort _ ->
       Some
         { pc_lhs = Pat.construct (lident (String.capitalize name)) None
         ; pc_guard = None
         ; pc_rhs = [%expr T T]
         }
     | _ -> None))
;;

let string_of_arg ~arg_count =
  match arg_count with
  | 0 -> (fun _ _ -> assert false)
  | 1 -> (fun prefix _ -> prefix)
  | _ -> (fun prefix i -> prefix ^ Int.to_string (i + 1))
;;

let gen_interface ~module_name external_abts defns : Ppxlib.Parsetree.structure =
  let external_abt_signatures =
    let arg_counts =
      List.map external_abts ~f:snd
      |> Int.Set.of_list
      |> Set.to_list
    in
    List.map arg_counts ~f:(fun arg_count ->
      let string_of_arg = string_of_arg ~arg_count in
      Str.modtype
        (Mtd.mk
           (ident (sprintf "External_abt%d" arg_count))
           ~typ:
             (Mty.signature
                ([ Sig.type_ Recursive
                     [ Type.mk
                         (ident "t")
                         ~params:
                           (List.init arg_count ~f:(fun arg ->
                              (Typ.var (string_of_arg "a" arg), Invariant)))
                         ~attrs:[deriving_sexp_attribute]
                     ]
                 ]
                 @
                 (match arg_count with
                  | 0 -> []
                  | _ ->
                    [ Sig.value
                        (Val.mk (ident "map")
                           (Typ.arrow Nolabel
                              (Typ.constr
                                 (lident "t")
                                 (List.init arg_count ~f:(fun arg -> Typ.var (string_of_arg "a" arg))))
                              (List.init arg_count ~f:(fun arg ->
                                 (Labelled (string_of_arg "f" arg),
                                  Typ.arrow Nolabel
                                    (Typ.var (string_of_arg "a" arg))
                                    (Typ.var (string_of_arg "b" arg))))
                               |> List.fold_right
                                    ~f:(fun (arg_label, arg_type) acc ->
                                      Typ.arrow arg_label arg_type acc)
                                    ~init:
                                      (Typ.constr
                                         (lident "t")
                                         (List.init arg_count ~f:(fun arg ->
                                            Typ.var (string_of_arg "b" arg)))))))
                    ; Sig.value
                        (Val.mk (ident "fold_map")
                           (Typ.arrow Nolabel
                              (Typ.constr
                                 (lident "t")
                                 (List.init arg_count ~f:(fun arg -> Typ.var (string_of_arg "a" arg))))
                              (Typ.arrow (Labelled "init")
                                 (Typ.var "acc")
                                 (List.init arg_count ~f:(fun arg ->
                                    (Labelled (string_of_arg "f" arg),
                                     Typ.arrow Nolabel
                                       (Typ.var "acc")
                                       (Typ.arrow Nolabel
                                          (Typ.var (string_of_arg "a" arg))
                                          (Typ.tuple
                                             [ Typ.var "acc"
                                             ; Typ.var (string_of_arg "b" arg)
                                             ]))))
                                  |> List.fold_right
                                       ~f:(fun (arg_label, arg_type) acc ->
                                         Typ.arrow arg_label arg_type acc)
                                       ~init:
                                         (Typ.tuple
                                            [ Typ.var "acc"
                                            ; Typ.constr
                                                (lident "t")
                                                (List.init arg_count ~f:(fun arg ->
                                                   Typ.var (string_of_arg "b" arg)))
                                            ])))))
                    ])))))
  in
  let per_defn_modl_decls =
    List.map defns ~f:(fun (name, defn) ->
      let module_type =
        match defn with
        | `Simple_abt _ as defn ->
          Mty.signature (shared_signature_items_of_defn ~current_name:name defn)
        | `Open_abt _ as defn ->
          Mty.signature (shared_signature_items_of_defn ~current_name:name defn)
        | `Closed_abt _ as defn ->
          Mty.signature
            ([ Sig.type_ Recursive
                 [ Type.mk (ident "t") ~attrs:[deriving_sexp_attribute] ]
             ]
             @ shared_signature_items_of_defn ~current_name:name defn)
        | `Symbol ->
          Mty.ident (lident "Temp_intf.S")
        | `Sort _ as defn ->
          Mty.signature
            ([ Sig.type_ Recursive
                 [ Type.mk (ident "t") ~attrs:[deriving_sexp_attribute] ]
             ; [%sigi: module Var : Temp_intf.S]
             ]
             @ shared_signature_items_of_defn ~current_name:name defn)
      in
      Md.mk (ident (Some (String.capitalize name))) module_type)
  in
  let modules =
    per_defn_modl_decls
    @
    [ Md.mk (ident (Some "Sort"))
        (Mty.signature
           [ Sig.type_ Recursive (sort_type defns) ])
    ]
  in
  [ [%stri open! Core]
  ; [%stri open! Abbot_runtime]
  ]
  @
  external_abt_signatures
  @
  [ [%stri type ('a, 'b) bind = 'a * 'b [@@deriving compare, sexp]] ]
  @
  (match external_abts with
   | [] ->
     [ Str.modtype (Mtd.mk (ident module_name) ~typ:(Mty.signature [ Sig.rec_module modules ])) ]
   | _::_ ->
     [ Str.modtype
         (Mtd.mk (ident "S")
            ~typ:
              (Mty.signature
                 (List.map external_abts
                    ~f:(fun (name, arg_count) ->
                      Sig.module_
                        (Md.mk
                           (ident (Some (String.capitalize name)))
                           (Mty.ident (lident (sprintf "External_abt%d" arg_count)))))
                  @
                  [ Sig.rec_module modules ])))
     ; Str.modtype
         (Mtd.mk
            (ident module_name)
            ~typ:
              (Mty.signature
                 [ Sig.module_
                     (Md.mk
                        (ident (Some "Make"))
                        (List.fold_right external_abts
                           ~f:(fun (name, arg_count) acc ->
                             Mty.functor_
                               (Named
                                  (ident (Some (String.capitalize name)),
                                   (Mty.ident (lident (sprintf "External_abt%d" arg_count)))))
                               acc)
                           ~init:
                             (Mty.with_
                                (Mty.ident (lident "S"))
                                ((List.map external_abts
                                    ~f:(fun (name, _) ->
                                      Pwith_modsubst
                                        (lident (String.capitalize name),
                                         lident (String.capitalize name))))))))
                 ]))
     ])
;;

let raise_internal_error_expr = [%expr failwith [%e internal_error_message]]

open
  Walks
    (struct
      let use_flat_names_internally = false
      let qualify_constructors = false
      let raise_internal_error_expr = raise_internal_error_expr
    end)

let refer_to_via_module = const true
let lang = `Ocaml

let gen_external_abt_modl_defn ~name ~arg_count =
  (* CR wduff: Some uses of [string_of_arg] should include the number even in the 1 case. *)
  let string_of_arg = string_of_arg ~arg_count in
  let type_defn =
    let args =
      List.init arg_count ~f:(fun arg -> Typ.var (string_of_arg "a" arg))
    in
    Str.type_ Recursive
      [ Type.mk (ident "t")
          ~params:(List.map args ~f:(fun arg_var -> (arg_var, Invariant)))
          ~manifest:(type_t ~via_module:true ~args name)
          ~attrs:[deriving_sexp_attribute]
      ]
  in
  let fold_map_defn =
    match arg_count with
    | 0 -> []
    | _ ->
      [%str
        let _fold_map =
          [%e
            List.fold_right (List.init arg_count ~f:Fn.id)
              ~f:(fun arg acc ->
                let fun_name = string_of_arg "f" arg in
                Exp.fun_ Nolabel None (pvar fun_name) acc)
              ~init:
                [%expr
                  fun init t ->
                    [%e
                      Exp.apply
                        (eident (String.capitalize name ^ ".fold_map"))
                        ([ (Nolabel, [%expr t])
                         ; (Labelled "init", [%expr init])
                         ]
                         @ List.map
                             (List.init arg_count ~f:Fn.id)
                             ~f:(fun arg ->
                               let fun_name = string_of_arg "f" arg in
                               (Labelled fun_name, eident fun_name)))
                    ]
                ]
          ]
      ]
  in
  let apply_subst_defn =
    let apply_subst_of_arg = string_of_arg "apply_subst" in
    [%stri
      let apply_subst =
        [%e
          match arg_count with
          | 0 -> [%expr fun _ t -> t]
          | _ ->
            List.fold_right (List.init arg_count ~f:Fn.id)
              ~f:(fun arg acc ->
                Exp.fun_ Nolabel None (Pat.var (ident (apply_subst_of_arg arg))) acc)
              ~init:
                [%expr
                  fun subst
                    (t :
                       [%t
                         Typ.constr
                           (lident "t")
                           (List.init arg_count ~f:(fun arg -> Typ.var (sprintf "a%d" arg)))])
                    : [%t
                    Typ.constr
                      (lident "t")
                      (List.init arg_count ~f:(fun arg -> Typ.var (sprintf "b%d" arg)))]
                    ->
                      [%e
                        Exp.apply
                          (eident (String.capitalize name ^ ".map"))
                          ((Nolabel, eident "t")
                           ::
                           List.init arg_count ~f:(fun arg ->
                             (Labelled (string_of_arg "f" arg),
                              [%expr
                                fun x ->
                                  [%e
                                    Exp.apply
                                      (eident (apply_subst_of_arg arg))
                                      [ (Nolabel, eident "subst"); (Nolabel, eident "x") ]]])))]]]]
  in
  let module_expr =
    Mod.structure
      (List.concat
         [ [ type_defn ]
         ; fold_map_defn
         ; [ apply_subst_defn ]
         ])
  in
  Str.module_ (Mb.mk (ident (Some (String.capitalize name))) module_expr)
;;

let gen_simple_abt_modl_defn ~name (`Simple_abt (args, cases) as defn) =
  let gen_fold_map = not (List.is_empty args) in
  let module_type =
    Mty.signature
      (shared_signature_items_of_defn ~current_name:name defn
       @
       (match gen_fold_map with
        | false -> []
        | true ->
          [ Sig.value
              (Val.mk
                 (ident "_fold_map")
                 (List.fold_right args
                    ~f:(fun arg acc ->
                      Typ.arrow Nolabel
                        (Typ.arrow Nolabel
                           (Typ.var "acc")
                           (Typ.arrow Nolabel
                              (Typ.var (arg ^ "1"))
                              (Typ.tuple [ Typ.var "acc"; Typ.var (arg ^ "2") ])))
                        acc)
                    ~init:
                      (Typ.arrow Nolabel
                         (Typ.var "acc")
                         (Typ.arrow Nolabel
                            (Typ.constr (lident "t")
                               (List.map args ~f:(fun arg -> Typ.var (arg ^ "1"))))
                            (Typ.tuple
                               [ Typ.var "acc"
                               ; Typ.constr (lident "t")
                                   (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
                               ])))))
          ])
       @
       [ Sig.value
            (Val.mk (ident "apply_subst")
               (List.fold_right args
                  ~f:(fun arg acc ->
                    Typ.arrow Nolabel
                      (Typ.arrow Nolabel
                         (Typ.constr (lident "GSS.Subst.t") [])
                         (Typ.arrow Nolabel
                            (Typ.var (arg ^ "1"))
                            (Typ.var (arg ^ "2"))))
                      acc)
                  ~init:
                    (Typ.arrow Nolabel
                       (Typ.constr (lident "GSS.Subst.t") [])
                       (Typ.arrow Nolabel
                          (Typ.constr (lident "t")
                             (List.map args ~f:(fun arg -> Typ.var (arg ^ "1"))))
                          (Typ.constr (lident "t")
                             (List.map args ~f:(fun arg -> Typ.var (arg ^ "2"))))))))
       ])
  in
  let module_expr =
    Mod.structure
      ([ [%stri open! GSS]
       ; Str.type_ Recursive
           [ Type.mk (ident "t")
               ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(exposed_type_of_abt
                                          ~use_temp_directly:false
                                          ~refer_to_via_module)))))))
               ~attrs:[deriving_sexp_attribute]
           ]
       ]
       @
       (match gen_fold_map with
        | false -> []
        | true ->
          [%str
           let _fold_map =
             [%e
               let cases = fold_map_code_for_simple_cases ~acc:[%expr acc] cases in
               let t1 =
                 Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "1")))
               in
               let t2 =
                 Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
               in
               List.fold_right args
                 ~f:(fun arg acc ->
                   [%expr fun [%p pvar ("f_" ^ arg)] -> [%e acc]])
                 ~init:
                   [%expr
                     fun acc (t : [%t t1]) : ('acc * [%t t2]) ->
                       [%e Exp.match_ [%expr t] cases]]]])
      @
      [ [%stri
        let apply_subst =
          [%e
            let (cases, used_subst) =
              apply_subst_code_for_simple_cases ~subst:[%expr subst] cases
            in
            let subst_pat =
              match used_subst with
              | `Used_subst -> pvar "subst"
              | `Ignored_subst -> pvar "_subst"
            in
            let t1 =
              Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "1")))
            in
            let t2 =
              Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
            in
            List.fold_right args
              ~f:(fun arg acc ->
                [%expr fun [%p pvar ("apply_subst_" ^ arg)] -> [%e acc]])
              ~init:
                [%expr
                  fun [%p subst_pat] (t : [%t t1]) : [%t t2] ->
                    [%e Exp.match_ [%expr t] cases]]]]
      ; [%stri
        let subst (type var) (type sort) =
          [%e
            List.fold_right args
              ~f:(fun arg acc ->
                Exp.fun_ Nolabel None (pvar ("subst_" ^ arg)) acc)
              ~init:
                [%expr fun (sort : (var, sort) Sort.t) (value : sort) (var : var) t ->
                  let (T T) = Sort.expose sort in
                  [%e
                    Exp.apply
                      [%expr apply_subst]
                      (List.map args ~f:(fun arg -> (Nolabel, eident ("subst_" ^ arg)))
                       @ [ (Nolabel, [%expr Subst.singleton sort value var])
                         ; (Nolabel, [%expr t])
                         ])
                  ]
                ]
          ]
        ;;
      ]
      ])
  in
  Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
;;

let gen_open_abt_modl_defn ~name (`Open_abt cases as defn) =
  let module_type =
    Mty.signature
      ([ [%sigi: type internal] ]
       @
       shared_signature_items_of_defn ~current_name:name defn
       @
       [ [%sigi: val into : t -> GSS.Packed_var.t list * internal]
       ; [%sigi: val out : internal -> GSS.Packed_var.t list * t]
       ; [%sigi: val apply_subst : GSS.Subst.t -> t -> t]
       ])
  in
  let module_expr =
    Mod.structure
      ([ [%stri open! GSS]
       ; Str.type_ Recursive
           [ Type.mk (ident "internal")
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(internal_type_of_abt ~refer_to_via_module ~lang)))))))
           ]
       ; Str.type_ Recursive
           [ Type.mk (ident "t")
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(exposed_type_of_abt
                                          ~use_temp_directly:false
                                          ~refer_to_via_module)))))
                    ))
               ~attrs:[deriving_sexp_attribute]
           ]
       ; [%stri
         let into (t : t) : GSS.Packed_var.t list * internal =
           [%e
             Exp.match_
               [%expr t]
               (into_code_for_open_cases
                  ~name_of_walked_value:name
                  cases)
           ]
       ]
       ; [%stri
         let out (internal : internal) : GSS.Packed_var.t list * t =
           [%e
             Exp.match_
               [%expr internal]
               (out_code_for_open_cases ~name_of_walked_value:name cases)
           ]
       ]
       ; [%stri
         let apply_subst =
           [%e
             let (cases, used_subst) =
               apply_subst_code_for_open_cases
                 ~subst:[%expr subst]
                 cases
             in
             let subst_pat =
               match used_subst with
               | `Used_subst -> pvar "subst"
               | `Ignored_subst -> pvar "_subst"
             in
             [%expr
               fun [%p subst_pat] t ->
                 [%e Exp.match_ [%expr t] cases]]
           ]
       ]
       ; [%stri
         let subst (type var) (type sort) (sort : (var, sort) Sort.t) (value : sort) (var : var) (t : t) : t =
           let (T T) = Sort.expose sort in
           apply_subst (Subst.singleton sort value var) t
         ;;
       ]
       ])
  in
  Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
;;

let gen_closed_abt_modl_defn ~name (`Closed_abt cases as defn) =
  let module_type =
    Mty.signature
      ([ [%sigi: type oper]
       ; Sig.type_ Recursive
           [ Type.mk (ident "t")
               ~manifest:[%type: oper GSS.With_subst.t]
               ~attrs:[deriving_sexp_attribute]
           ]
       ]
       @
       shared_signature_items_of_defn ~current_name:name defn)
  in
  let module_expr =
    Mod.structure
      ([ [%stri open! GSS]
       ; Str.type_ Recursive
           [ Type.mk (ident "oper")
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(internal_type_of_abt ~refer_to_via_module ~lang)))))))
           ]
       ; [%stri type t = oper GSS.With_subst.t]
       ; Str.type_ Recursive
           [ Type.mk (ident "view")
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(exposed_type_of_abt
                                          ~use_temp_directly:false
                                          ~refer_to_via_module)))))
                    ))
               ~attrs:[deriving_sexp_attribute]
           ]
       ; [%stri
         let into (view : view) : t =
           let (oper : oper) =
             [%e
               Exp.match_
                 [%expr view]
                 (into_code_for_closed_cases
                    ~name_of_walked_value:name
                    cases)
             ]
           in
           (Subst.ident, oper)
       ]
       ; (let (oper_cases_expr, used_subst) =
            out_code_for_closed_cases
              ~name_of_walked_value:name
              ~subst:[%expr subst]
              cases
          in
          (* CR wduff: Shouldn't we not store substs that aren't gonna be used at all? *)
          let subst_pat =
            match used_subst with
            | `Used_subst -> [%pat? subst]
            | `Ignored_subst -> [%pat? _subst]
          in
          [%stri
            let out ([%p subst_pat], oper) : view =
              [%e Exp.match_ [%expr (oper : oper)] oper_cases_expr]
          ])
       ]
       @
       convenient_constructors_impl ~keywords ~is_sort:false cases
       @
       [ [%stri let sexp_of_t t = [%sexp_of: view] (out t)]
       ; [%stri
         let subst (type var) (type sort) (sort : (var, sort) Sort.t) (value : sort) (var : var) (t : t) : t =
           let (T T) = Sort.expose sort in
           With_subst.apply_subst (Subst.singleton sort value var) t
         ;;
       ]
       ])
  in
  Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
;;

let gen_symbol_modl_defn ~name =
  Mod.constraint_
    (Mod.ident (lident "Temp"))
    (Mty.with_
       (Mty.ident (lident "Temp_intf.S"))
       [ Pwith_type
           (lident "t", Type.mk (ident "t") ~manifest:(Typ.constr (lident "Temp.t") []))
       ])
  |> Mb.mk (ident (Some (String.capitalize name)))
;;

let gen_sort_modl_defn ~name (`Sort cases as defn) =
  let module_type =
    Mty.signature
      ([ [%sigi: module Var = Temp]
       ; [%sigi: type oper]
       ; Sig.type_ Recursive
           [ Type.mk (ident "t")
               ~manifest:[%type: (Var.t, oper) GSS.Generic_sort.t]
               ~attrs:[deriving_sexp_attribute]
           ]
       ]
       @
       shared_signature_items_of_defn ~current_name:name defn)
  in
  let module_expr =
    Mod.structure
      ([ [%stri open GSS]
       ; [%stri module Var = Temp]
       ; Str.type_ Recursive
           [ Type.mk (ident "view")
               ~kind:
                 (Ptype_variant
                    (Type.constructor
                       (ident "Var")
                       ~args:(Pcstr_tuple [type_var ~via_module:true name])
                     :: List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(exposed_type_of_abt
                                          ~use_temp_directly:false
                                          ~refer_to_via_module)))))
                    ))
               ~attrs:[deriving_sexp_attribute]
           ]
       ; Str.type_ Recursive
           [ Type.mk (ident "oper")
               ~kind:
                 (Ptype_variant
                    (List.map cases ~f:(fun (constructor_name, abt) ->
                       Type.constructor
                         (ident constructor_name)
                         ~args:
                           (Pcstr_tuple
                              (Option.to_list
                                 (Option.map abt
                                    ~f:(internal_type_of_abt ~refer_to_via_module ~lang)))))))
           ]
       ; [%stri type t = (Var.t, oper) Generic_sort.t]
       ; [%stri
         let into (view : view) : t =
           [%e
             Exp.match_
               [%expr view]
               ({ pc_lhs = [%pat? Var var]
                ; pc_guard = None
                ; pc_rhs = [%expr Generic_sort.var var]
                }
                :: List.map
                     (into_code_for_closed_cases
                        ~name_of_walked_value:name
                        cases)
                     ~f:(fun { pc_lhs; pc_guard; pc_rhs } ->
                       { pc_lhs; pc_guard; pc_rhs = [%expr Generic_sort.oper [%e pc_rhs]] }))
           ]
       ]
       ; (let (oper_cases_expr, used_subst) =
            out_code_for_closed_cases
              ~name_of_walked_value:name
              ~subst:[%expr subst]
              cases
          in
          (* CR wduff: Shouldn't we not store substs that aren't gonna be used at all? *)
          let subst_pat =
            match used_subst with
            | `Used_subst -> [%pat? subst]
            | `Ignored_subst -> [%pat? _subst]
          in
          [%stri
            let out (t : t) : view =
              match t with
              | Var (Bound_var _) -> [%e raise_internal_error_expr]
              | Var (Free_var var) -> Var var
              | Oper ([%p subst_pat], oper) ->
                [%e Exp.match_ [%expr oper] oper_cases_expr]
          ])
       ]
       @
       convenient_constructors_impl ~keywords ~is_sort:true cases
       @
       [ [%stri let sexp_of_t t = [%sexp_of: view] (out t)] ]
       @
       [ [%stri
         let subst (type var) (type sort) (sort : (var, sort) Sort.t) (value : sort) (var : var) (t : t) : t =
           let (T T) = Sort.expose sort in
           Generic_sort.apply_subst
             [%e Exp.construct (lident (String.capitalize name)) None]
             (Subst.singleton sort value var)
             t
         ;;
       ]
       ])
  in
  Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
;;

let gen_implementation ~module_name external_abts defns : Ppxlib.Parsetree.structure =
  let external_abt_modl_defns =
    List.map external_abts ~f:(fun (name, arg_count) ->
      gen_external_abt_modl_defn ~name ~arg_count)
  in
  let per_defn_modl_defns =
    List.map defns ~f:(fun (name, defn) ->
      match defn with
      | `Simple_abt _ as defn -> gen_simple_abt_modl_defn ~name defn
      | `Open_abt _ as defn -> gen_open_abt_modl_defn ~name defn
      | `Closed_abt _ as defn -> gen_closed_abt_modl_defn ~name defn
      | `Symbol -> gen_symbol_modl_defn ~name
      | `Sort _ as defn -> gen_sort_modl_defn ~name defn)
  in
  let body =
    external_abt_modl_defns
    @
    [ Str.rec_module
        (per_defn_modl_defns
         @ [ Mb.mk (ident (Some "Sort"))
               (Mod.constraint_
                  (Mod.structure
                     [ Str.type_ Recursive (sort_type defns)
                     ; [%stri
                       let same_witness
                             (type var1 sort1 var2 sort2)
                             (t1 : (var1, sort1) t)
                             (t2 : (var2, sort2) t)
                         : ((var1, var2) Type_equal.t * (sort1, sort2) Type_equal.t) option =
                         [%e
                           Exp.match_
                             [%expr (t1, t2)]
                             (sort_same_witness_cases defns
                              @ [ { pc_lhs = [%pat? _]; pc_guard = None; pc_rhs = [%expr None] } ])]
                     ]
                     ; [%stri
                       module Sort_is_generic = struct
                         type ('var, 'sort) t = T : ('sort, ('var, _) GSS.Generic_sort.t) Type_equal.t -> ('var, 'sort) t
                       end
                     ]
                     ; [%stri
                        let expose
                              (type var sort)
                              (sort : (var, sort) Sort.t)
                          : (var, sort) Sort_is_generic.t =
                          [%e Exp.match_ [%expr sort] (to_sort_or_symbol_eq_cases defns)]]
                     ])
                  (Mty.signature
                     [ Sig.type_ Recursive (sort_type defns)
                     ; [%sigi: include Sort_intf.S with type ('var, 'sort) t := ('var, 'sort) t]
                     ; [%sigi:
                       module Sort_is_generic : sig
                         type ('var, 'sort) t = T : ('sort, ('var, _) GSS.Generic_sort.t) Type_equal.t -> ('var, 'sort) t
                       end]
                     ; [%sigi: val expose : ('var, 'sort) Sort.t -> ('var, 'sort) Sort_is_generic.t]
                     ]))
           ; Mb.mk (ident (Some "GSS"))
               (Mod.constraint_
                  (Mod.apply
                     (Mod.ident (lident "Generic_sort_and_subst.Make"))
                     (Mod.ident (lident "Sort")))
                  (Mty.with_
                     (Mty.ident (lident "Generic_sort_and_subst.S"))
                     [ Pwith_typesubst
                         (lident "sort",
                          Type.mk
                            (ident "sort")
                            ~params:[ ([%type: 'var], Invariant); ([%type: 'sort], Invariant) ]
                            ~manifest:[%type: ('var, 'sort) Sort.t])
                     ]))
           ])
    ]
  in
  [ [%stri open! Core]
  ; [%stri open! Abbot_runtime]
  ; Str.open_ (Opn.mk ~override:Override (Mod.ident (lident (module_name ^ "_intf"))))
  ]
  @
  (match external_abts with
   | [] -> body
   | _::_ ->
     [ Str.module_
         (Mb.mk
            (ident (Some "Make"))
            (List.fold_right external_abts
               ~init:(Mod.structure body)
               ~f:(fun (name, arg_count) acc ->
                 Mod.functor_
                   (Named
                      (ident (Some (String.capitalize name)),
                       Mty.ident (lident (sprintf "External_abt%d" arg_count))))
                   acc)))
     ])
;;

let gen_ast ~module_name (defns : Defn.t list) =
  let (external_abts, defns) =
    List.partition_map defns ~f:(fun { name; args; body } ->
      match body with
      | External_simple_abt ->
        First (name, args)
      | Internal_abt (T (Simple, cases)) ->
        Second (name, `Simple_abt (args, (cases : [ `Simple ] Cases.t)))
      | Internal_abt (T (Open, cases)) ->
        begin
          match args with
          | [] -> ()
          | _::_ ->
            (* CR wduff: Better error. *)
            raise_s [%message ""]
        end;
        Second (name, `Open_abt (cases : [ `Open ] Cases.t))
      | Internal_abt (T (Closed, cases)) ->
        begin
          match args with
          | [] -> ()
          | _::_ ->
            (* CR wduff: Better error. *)
            raise_s [%message ""]
        end;
        Second (name, `Closed_abt (cases : [ `Closed ] Cases.t))
      | Symbol ->
        begin
          match args with
          | [] -> ()
          | _::_ ->
            (* CR wduff: Better error. *)
            raise_s [%message ""]
        end;
        Second (name, `Symbol)
      | Sort cases ->
        begin
          match args with
          | [] -> ()
          | _::_ ->
            (* CR wduff: Better error. *)
            raise_s [%message ""]
        end;
        Second (name, `Sort cases))
  in
  let external_abts =
    List.map external_abts ~f:(fun (name, args) -> (name, List.length args))
  in
  (gen_interface ~module_name external_abts defns,
   gen_implementation ~module_name external_abts defns)
;;
