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

let gen_implementation ~module_name external_abts defns : Ppxlib.Parsetree.structure =
  let refer_to_via_module = const true in
  let lang = `Ocaml in
  let external_abt_modl_defns =
    List.map external_abts ~f:(fun (name, arg_count) ->
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
      let map_defn =
        let t1 =
          Typ.constr
            (lident "t")
            (List.init arg_count ~f:(fun arg -> Typ.var (string_of_arg "a" arg)))
        in
        let t2 =
          Typ.constr
            (lident "t")
            (List.init arg_count ~f:(fun arg -> Typ.var (string_of_arg "b" arg)))
        in
        (match arg_count with
         | 0 -> []
         | _ ->
           [%str
             let map (t : [%t t1]) =
               [%e
                 List.fold_right (List.init arg_count ~f:Fn.id)
                   ~f:(fun arg acc ->
                     let fun_name = string_of_arg "f" arg in
                     Exp.fun_ (Labelled fun_name) None (pvar fun_name) acc)
                   ~init:
                     [%expr
                       let ((), (t : [%t t2])) =
                         [%e
                           Exp.apply
                             (eident (String.capitalize name ^ ".fold_map"))
                             ((Nolabel, eident "t")
                              ::
                              (Labelled "init", [%expr ()])
                              ::
                              List.init arg_count ~f:(fun arg ->
                                let arg_var = string_of_arg "arg" arg in
                                (Labelled (string_of_arg "f" arg),
                                 [%expr
                                   fun () [%p pvar arg_var] ->
                                     ((), [%e eident (string_of_arg "f" arg)] [%e eident arg_var])])))]
                       in
                       t]]])
      in
      let apply_renaming_defn =
        let apply_renaming_of_arg = string_of_arg "apply_renaming" in
        [%stri
          let apply_renaming =
            [%e
               (* CR wduff: Checking for 0 here is a dumb way to deal with the unused variable
                  issue, because an phantom type argument could also cause that. *)
              (match arg_count with
               | 0 -> [%expr fun _ acc t -> (acc, t)]
               | _ ->
                 List.fold_right (List.init arg_count ~f:Fn.id)
                   ~f:(fun arg acc ->
                     Exp.fun_ Nolabel None (Pat.var (ident (apply_renaming_of_arg arg))) acc)
                   ~init:
                     [%expr
                       fun renaming acc
                         (t :
                            [%t
                              Typ.constr
                                (lident "t")
                                (List.init arg_count ~f:(fun arg -> Typ.var (sprintf "a%d" arg)))])
                         ->
                           ([%e
                             Exp.apply
                               (eident (String.capitalize name ^ ".fold_map"))
                               ((Nolabel, eident "t")
                                ::
                                (Labelled "init", eident "acc")
                                ::
                                List.init arg_count ~f:(fun arg ->
                                  (Labelled (string_of_arg "f" arg),
                                   Exp.apply
                                     (eident (apply_renaming_of_arg arg))
                                     [ (Nolabel, eident "renaming") ])))]
                            : 'acc
                              * [%t
                                Typ.constr
                                  (lident "t")
                                  (List.init arg_count ~f:(fun arg -> Typ.var (sprintf "b%d" arg)))])])]]
      in
      let subst_defn =
        let subst_of_arg = string_of_arg "subst" in
        [%stri
          let subst =
            [%e
              (match arg_count with
               | 0 -> [%expr fun _ _ _ t -> t]
               | _ ->
                 List.fold_right (List.init arg_count ~f:Fn.id)
                   ~f:(fun arg acc ->
                     Exp.fun_ Nolabel None (Pat.var (ident (subst_of_arg arg))) acc)
                   ~init:
                     [%expr
                       fun sort value var t ->
                         [%e
                           Exp.apply
                             (eident "map")
                             ((Nolabel, eident "t")
                              ::
                              List.init arg_count ~f:(fun arg ->
                                (Labelled (string_of_arg "f" arg),
                                 [%expr [%e eident (subst_of_arg arg)] sort value var])))]
                     ])]]
      in
      let module_expr =
        Mod.structure
          ([ type_defn ]
           @
           map_defn
           @
           [  apply_renaming_defn
           ; subst_defn
           ])
      in
      Str.module_ (Mb.mk (ident (Some (String.capitalize name))) module_expr))
  in
  let per_defn_modl_defns =
    List.map defns ~f:(fun (name, defn) ->
      match defn with
      | `Simple_abt (args, cases) as defn ->
        (* CR wduff: Implement map for simple abts. *)
        let module_type =
          Mty.signature
            (shared_signature_items_of_defn ~current_name:name defn
             @
             [ Sig.value
                 (Val.mk (ident "apply_renaming")
                    (List.fold_right args
                       ~f:(fun arg acc ->
                         Typ.arrow Nolabel
                           (Typ.arrow Nolabel
                              (Typ.constr (lident "Renaming.t") [])
                              (Typ.arrow Nolabel
                                 (Typ.var "acc")
                                 (Typ.arrow Nolabel
                                    (Typ.var (arg ^ "1"))
                                    (Typ.tuple [ Typ.var "acc"; Typ.var (arg ^ "2") ]))))
                           acc)
                       ~init:
                         (Typ.arrow Nolabel
                            (Typ.constr (lident "Renaming.t") [])
                            (Typ.arrow Nolabel
                               (Typ.var "acc")
                               (Typ.arrow Nolabel
                                  (Typ.constr (lident "t")
                                     (List.map args ~f:(fun arg -> Typ.var (arg ^ "1"))))
                                  (Typ.tuple
                                     [ Typ.var "acc"
                                     ; Typ.constr (lident "t")
                                         (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
                                     ]))))))
             ])
        in
        let module_expr =
          Mod.structure
            ([ Str.type_ Recursive
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
                                                ~refer_to_via_module)))))
                          ))
                     ~attrs:[deriving_sexp_attribute]
                 ]
             ; [%stri
               let apply_renaming =
                 [%e
                   let (cases, used_renaming) =
                     apply_renaming_code_for_simple_cases
                       ~renaming:[%expr renaming]
                       ~acc:[%expr acc]
                       cases
                   in
                   let renaming_pat =
                     match used_renaming with
                     | `Used_renaming -> pvar "renaming"
                     | `Ignored_renaming -> pvar "_renaming"
                   in
                   let t1 =
                     Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "1")))
                   in
                   let t2 =
                     Typ.constr (lident "t") (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
                   in
                   List.fold_right args
                     ~f:(fun arg acc ->
                       [%expr fun [%p pvar ("apply_renaming_" ^ arg)] -> [%e acc]])
                     ~init:
                       [%expr
                         fun [%p renaming_pat] acc (t : [%t t1]) : ('acc * [%t t2]) ->
                           [%e Exp.match_ [%expr t] cases]]
                 ]
             ]
             ; [%stri
               let subst =
                 [%e
                   let (cases, used_sub) =
                     subst_code_for_cases
                       ~name_of_walked_value:name
                       ~sub:[ (Nolabel, "sort"); (Nolabel, "value"); (Nolabel, "var") ]
                       cases
                   in
                   let sort_pat =
                     match used_sub with
                     | `Used_sub -> pvar "sort"
                     | `Ignored_sub -> pvar "_sort"
                   in
                   let value_pat =
                     match used_sub with
                     | `Used_sub -> pvar "value"
                     | `Ignored_sub -> pvar "_value"
                   in
                   let var_pat =
                     match used_sub with
                     | `Used_sub -> pvar "var"
                     | `Ignored_sub -> pvar "_var"
                   in
                   List.fold_right args
                     ~f:(fun arg acc ->
                       Exp.fun_ Nolabel None (Pat.var (ident ("subst_" ^ arg))) acc)
                     ~init:
                       [%expr
                         fun [%p sort_pat] [%p value_pat] [%p var_pat] t ->
                           [%e Exp.match_ [%expr t] cases ]]]]
             ])
        in
        Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
      | `Open_abt cases as defn ->
        let module_type =
          Mty.signature
            ([ [%sigi: type oper]
             ; [%sigi: type internal = oper With_renaming.t]
             ]
             @
             shared_signature_items_of_defn ~current_name:name defn
             @
             [ [%sigi: val into : t -> Temp.t list * internal]
             ; [%sigi: val out : internal -> Temp.t list * t]
             ])
        in
        let module_expr =
          Mod.structure
            ([ Str.type_ Recursive
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
             ; [%stri type internal = oper With_renaming.t]
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
               let into (t : t) : Temp.t list * internal =
                 let (vars, (oper : oper)) =
                   [%e
                     Exp.match_
                       [%expr t]
                       (into_code_for_open_cases
                          ~name_of_walked_value:name
                          cases)
                   ]
                 in
                 (vars, (Renaming.ident, oper))
             ]
             ; [%stri
               let out (renaming, oper) : Temp.t list * t =
                 [%e
                   Exp.match_
                     [%expr (oper : oper)]
                     (out_code_for_open_cases
                        ~name_of_walked_value:name
                        cases)
                 ]
             ]
             ; (let (cases, used_sub) =
                  subst_code_for_cases
                    ~name_of_walked_value:name
                    ~sub:[ (Nolabel, "sort"); (Nolabel, "value"); (Nolabel, "var") ]
                    cases
                in
                let sort_pat =
                  match used_sub with
                  | `Used_sub -> pvar "sort"
                  | `Ignored_sub -> pvar "_sort"
                in
                let value_pat =
                  match used_sub with
                  | `Used_sub -> pvar "value"
                  | `Ignored_sub -> pvar "_value"
                in
                let var_pat =
                  match used_sub with
                  | `Used_sub -> pvar "var"
                  | `Ignored_sub -> pvar "_var"
                in
                [%stri
                  let subst [%p sort_pat] [%p value_pat] [%p var_pat] t =
                    [%e Exp.match_ [%expr t] cases]
                ])
             ])
        in
        Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
      | `Closed_abt cases as defn ->
        let module_type =
          Mty.signature
            ([ [%sigi: type oper]
             ; Sig.type_ Recursive
                 [ Type.mk (ident "t")
                     ~manifest:[%type: oper With_renaming.t]
                     ~attrs:[deriving_sexp_attribute]
                 ]
             ]
             @
             shared_signature_items_of_defn ~current_name:name defn)
        in
        let module_expr =
          Mod.structure
            ([ Str.type_ Recursive
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
             ; [%stri type t = oper With_renaming.t]
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
                 (Renaming.ident, oper)
             ]
             ; [%stri
               let out (renaming, oper) : view =
                 [%e
                   Exp.match_
                     [%expr (oper : oper)]
                     (out_code_for_closed_cases
                        ~name_of_walked_value:name
                        cases)
                 ]
             ]
             ]
             @
             convenient_constructors_impl ~keywords ~is_sort:false cases
             @
             [ [%stri let sexp_of_t t = [%sexp_of: view] (out t)] ]
             @
             [ (let (cases, used_sub) =
                  subst_code_for_cases
                    ~name_of_walked_value:name
                    ~sub:[ (Nolabel, "sort"); (Nolabel, "value"); (Nolabel, "var") ]
                    cases
                in
                let sort_pat =
                  match used_sub with
                  | `Used_sub -> pvar "sort"
                  | `Ignored_sub -> pvar "_sort"
                in
                let value_pat =
                  match used_sub with
                  | `Used_sub -> pvar "value"
                  | `Ignored_sub -> pvar "_value"
                in
                let var_pat =
                  match used_sub with
                  | `Used_sub -> pvar "var"
                  | `Ignored_sub -> pvar "_var"
                in
                [%stri
                  let subst [%p sort_pat] [%p value_pat] [%p var_pat] t =
                    let view = [%e Exp.match_ [%expr out t] cases] in
                    into view])
             ])
        in
        Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type)
      | `Symbol ->
        Mod.constraint_
          (Mod.ident (lident "Temp"))
          (Mty.with_
             (Mty.ident (lident "Temp_intf.S"))
             [ Pwith_type
                 (lident "t", Type.mk (ident "t") ~manifest:(Typ.constr (lident "Temp.t") []))
             ])
        |> Mb.mk (ident (Some (String.capitalize name)))
      | `Sort cases as defn ->
        let module_type =
          Mty.signature
            ([ [%sigi: type oper]
             ; Sig.type_ Recursive
                 [ Type.mk (ident "t")
                     ~manifest:[%type: oper Internal_sort.t]
                     ~attrs:[deriving_sexp_attribute]
                 ]
             ; [%sigi: module Var = Temp]
             ]
             @
             shared_signature_items_of_defn ~current_name:name defn)
        in
        let module_expr =
          Mod.structure
            ([ [%stri module Var = Temp]
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
             ; [%stri type t = oper Internal_sort.t]
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
             ; [%stri
               let into (view : view) : t =
                 [%e
                   Exp.match_
                     [%expr view]
                     ({ pc_lhs = [%pat? Var var]
                      ; pc_guard = None
                      ; pc_rhs = [%expr Var (Free_var var)]
                      }
                      :: List.map
                           (into_code_for_closed_cases
                              ~name_of_walked_value:name
                              cases)
                           ~f:(fun { pc_lhs; pc_guard; pc_rhs } ->
                             { pc_lhs; pc_guard; pc_rhs = [%expr Oper (Renaming.ident, [%e pc_rhs])] }))
                 ]
             ]
             ; [%stri
               let out (t : t) : view =
                 match t with
                 | Var (Bound_var _) -> [%e raise_internal_error_expr]
                 | Var (Free_var var) -> Var var
                 | Oper (renaming, oper) ->
                   [%e
                     Exp.match_
                       [%expr oper]
                       (out_code_for_closed_cases
                          ~name_of_walked_value:name
                          cases)
                   ]
             ]
             ]
             @
             convenient_constructors_impl ~keywords ~is_sort:true cases
             @
             [ [%stri let sexp_of_t t = [%sexp_of: view] (out t)] ]
             @
             [ (let (cases, used_sub) =
                  subst_code_for_cases
                    ~name_of_walked_value:name
                    ~sub:[ (Nolabel, "sort"); (Nolabel, "value"); (Nolabel, "var") ]
                    cases
                in
                let sort_pat =
                  match used_sub with
                  | `Used_sub -> pvar "sort"
                  | `Ignored_sub -> pvar "_sort"
                in
                let value_pat =
                  match used_sub with
                  | `Used_sub -> pvar "value"
                  | `Ignored_sub -> pvar "_value"
                in
                let var_pat =
                  match used_sub with
                  | `Used_sub -> pvar "var"
                  | `Ignored_sub -> pvar "_var"
                in
                [%stri
                  let subst
                        (type var)
                        (type sort)
                        ([%p sort_pat] : (var, sort) Sort.t)
                        ([%p value_pat] : sort)
                        ([%p var_pat] : var)
                        (t : t)
                    : t =
                    [%e Exp.match_
                          [%expr out t]
                          ({ pc_lhs =
                               Pat.construct
                                 (lident "Var")
                                 (Some (Pat.var (ident "var'")))
                           ; pc_guard = None
                           ; pc_rhs =
                               Exp.match_
                                 [%expr sort]
                                 ({ pc_lhs =
                                      Pat.construct
                                        (lident ("Sort." ^ String.capitalize name))
                                        None
                                  ; pc_guard = None
                                  ; pc_rhs =
                                      Exp.match_
                                        [%expr Temp.equal var var']
                                        [ { pc_lhs = Pat.construct (lident "true") None
                                          ; pc_guard = None
                                          ; pc_rhs = eident "value"
                                          }
                                        ; { pc_lhs = Pat.construct (lident "false") None
                                          ; pc_guard = None
                                          ; pc_rhs = eident "t"
                                          }
                                        ]
                                  }
                                  ::
                                  (match
                                     List.count defns ~f:(function (_, `Sort _) -> true | _ -> false)
                                   with
                                   | 1 ->
                                     (* If there is exactly one sort, we drop this case to avoid a
                                        redunant match warning. *)
                                     []
                                   | _ ->
                                     [ { pc_lhs = Pat.any ()
                                       ; pc_guard = None
                                       ; pc_rhs = eident "t"
                                       }
                                     ]))
                           }
                           ::
                           (List.map cases ~f:(fun { pc_lhs; pc_guard; pc_rhs } ->
                              { pc_lhs
                              ; pc_guard
                              ; pc_rhs =
                                  [%expr [%e pc_rhs] |> into]
                              })))
                    ]
                ])
             ])
        in
        Mb.mk (ident (Some (String.capitalize name))) (Mod.constraint_ module_expr module_type))
  in
  let body =
    external_abt_modl_defns
    @
    [ Str.rec_module
        (per_defn_modl_defns
         @ [ Mb.mk (ident (Some "Sort"))
               (Mod.constraint_
                  (Mod.structure
                     [ Str.type_ Recursive (sort_type defns) ])
                  (Mty.signature
                     [ Sig.type_ Recursive (sort_type defns) ]))
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
