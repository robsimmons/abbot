open! Core
open Ppxlib
open Ast_helper
open Typed
open Ast_gen_shared

let loc = Location.none

module Dependency = struct
  module T = struct
    type t = [ `Direct | `Var ] * string [@@deriving compare, sexp_of]
  end

  include T
  include Comparable.Make_plain (T)
end

module Context = struct
  type t =
    { structure_name : string
    ; compare_declaration_order : string -> string -> Ordering.t
    ; dependencies : Dependency.Set.t String.Table.t
    }
end

let keywords =
  String.Set.of_list
    [ "abstype"
    ; "and"
    ; "andalso"
    ; "as"
    ; "case"
    ; "datatype"
    ; "do"
    ; "else"
    ; "end"
    ; "eqtype"
    ; "exception"
    ; "fn"
    ; "fun"
    ; "functor"
    ; "handle"
    ; "if"
    ; "in"
    ; "include"
    ; "infix"
    ; "infixr"
    ; "let"
    ; "local"
    ; "nil"
    ; "nonfix"
    ; "of"
    ; "op"
    ; "open"
    ; "orelse"
    ; "raise"
    ; "rec"
    ; "sharing"
    ; "signature"
    ; "struct"
    ; "structure"
    ; "then"
    ; "type"
    ; "val"
    ; "where"
    ; "while"
    ; "with"
    ; "withtype"
    ]
;;

let subst_function_signature_item ~args =
  let t_with_args = Typ.constr (lident "t") (List.map args ~f:Typ.var) in
  let core_type =
    List.fold_right args
      ~f:(fun arg acc ->
        Typ.arrow Nolabel [%type: subst -> [%t Typ.var arg] -> [%t Typ.var arg]] acc)
      ~init:[%type: subst -> [%t t_with_args] -> [%t t_with_args]]
  in
  [%sigi: val subst : [%t core_type]]
;;

let subst_type (sorts : string list) =
  [ Type.mk
      (ident "t")
      ~kind:
        (Ptype_variant
           (List.map sorts ~f:(fun name ->
              Type.constructor
                (ident (String.capitalize name))
                ~args:
                  (Pcstr_tuple
                     [ type_t ~via_module:true name
                     ; type_var ~via_module:true name
                     ]))))
  ]
;;

let gen_interface (context : Context.t) (defns : Defn.t list) : Ppxlib.Parsetree.structure =
  let per_defn_modl_decls =
    List.map defns ~f:(fun { name; args; body } ->
      let refer_to_via_module name' =
        match context.compare_declaration_order name name' with
        | Less | Equal -> false
        | Greater -> true
      in
      let module_type =
        match body with
        | External_simple_abt ->
          let abstract_types_for_sharing =
            [%sigi: type subst]
            :: (Hashtbl.find_exn context.dependencies name
                |> Set.to_list
                |> List.filter ~f:(fun (_sort, name') ->
                  match context.compare_declaration_order name name' with
                  | Less -> true
                  | Equal | Greater -> false)
                |> List.map ~f:(fun (sort, name') ->
                  Sig.type_ Recursive
                    [ Type.mk
                        (ident
                           (match sort with
                            | `Direct -> name'
                            | `Var -> name' ^ "Var"))
                    ]))
          in
          Mty.signature
            (abstract_types_for_sharing
             @
             [ Sig.type_ Recursive
                 [ Type.mk (ident "t")
                     ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                 ]
             ; subst_function_signature_item ~args
             ])
        | Symbol ->
          begin
            match args with
            | [] -> ()
            | _::_ ->
              (* CR wduff: Better error. *)
              raise_s [%message ""]
          end;
          Mty.ident (lident "TEMP")
        | Internal_abt (T (Simple, cases)) ->
          let abstract_types_for_sharing =
            [%sigi: type subst]
            :: (Hashtbl.find_exn context.dependencies name
                |> Set.to_list
                |> List.filter ~f:(fun (_sort, name') ->
                  match context.compare_declaration_order name name' with
                  | Less -> true
                  | Equal | Greater -> false)
                |> List.map ~f:(fun (sort, name') ->
                  Sig.type_ Recursive
                    [ Type.mk
                        (ident
                           (match sort with
                            | `Direct -> name'
                            | `Var -> name' ^ "Var"))
                    ]))
          in
          Mty.signature
            (abstract_types_for_sharing
             @ [ Sig.type_ Recursive
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
                                                  ~use_temp_directly:true
                                                  ~refer_to_via_module)))))))
                   ; Type.mk (ident name)
                       ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                       ~manifest:(Typ.constr (lident "t") (List.map args ~f:Typ.var))
                   ]
               ; subst_function_signature_item ~args
               ])
        | Internal_abt (T (Open, cases)) ->
          begin
            match args with
            | [] -> ()
            | _::_ ->
              (* CR wduff: Better error. *)
              raise_s [%message ""]
          end;
          let abstract_types_for_sharing =
            [%sigi: type subst]
            :: (Hashtbl.find_exn context.dependencies name
                |> Set.to_list
                |> List.filter ~f:(fun (_sort, name') ->
                  match context.compare_declaration_order name name' with
                  | Less -> true
                  | Equal | Greater -> false)
                |> List.map ~f:(fun (sort, name') ->
                  Sig.type_ Recursive
                    [ Type.mk
                        (ident
                           (match sort with
                            | `Direct -> name'
                            | `Var -> name' ^ "Var"))
                    ]))
          in
          Mty.signature
            (abstract_types_for_sharing
             @ [ Sig.type_ Recursive
                   [ type_decl_of_cases
                       ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
                       ~deriving_sexp:false
                       ~name:"t"
                       cases
                   ; Type.mk (ident name) ~manifest:[%type: t]
                   ]
               ; subst_function_signature_item ~args:[]
               ])
        | Internal_abt (T (Closed, cases)) ->
          begin
            match args with
            | [] -> ()
            | _::_ ->
              (* CR wduff: Better error. *)
              raise_s [%message ""]
          end;
          let abstract_types_for_sharing =
            [%sigi: type subst]
            :: (Hashtbl.find_exn context.dependencies name
                |> Set.to_list
                |> List.filter ~f:(fun (_sort, name') ->
                  match context.compare_declaration_order name name' with
                  | Less -> true
                  | Equal | Greater -> false)
                |> List.map ~f:(fun (sort, name') ->
                  Sig.type_ Recursive
                    [ Type.mk
                        (ident
                           (match sort with
                            | `Direct -> name'
                            | `Var -> name' ^ "Var"))
                    ]))
          in
          Mty.signature
            (abstract_types_for_sharing
             @ [ Sig.type_ Recursive [ Type.mk (ident "t") ]
               ; Sig.type_ Recursive
                   [ Type.mk (ident name) ~manifest:[%type: t] ]
               ; Sig.type_ Recursive
                   [ type_decl_of_cases
                       ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
                       ~deriving_sexp:false
                       ~name:"view"
                       cases
                   ]
               ]
             @
             view_conversion_intf
             @
             convenient_constructors_intf
               ~keywords
               ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
               ~is_sort:false
               cases
             @
             [ subst_function_signature_item ~args:[] ])
        | Sort cases ->
          begin
            match args with
            | [] -> ()
            | _::_ ->
              (* CR wduff: Better error. *)
              raise_s [%message ""]
          end;
          let abstract_types_for_sharing =
            [%sigi: type subst]
            :: (Hashtbl.find_exn context.dependencies name
                |> Set.to_list
                |> List.filter ~f:(fun (_sort, name') ->
                  match context.compare_declaration_order name name' with
                  | Less -> true
                  | Equal | Greater -> false)
                |> List.map ~f:(fun (sort, name') ->
                  Sig.type_ Recursive
                    [ Type.mk
                        (ident
                           (match sort with
                            | `Direct -> name'
                            | `Var -> name' ^ "Var"))
                    ]))
          in
          Mty.signature
            (abstract_types_for_sharing
             @ [ Sig.type_ Recursive [ Type.mk (ident "t") ]
               ; Sig.type_ Recursive [ Type.mk (ident name) ~manifest:[%type: t] ]
               ; [%sigi: module Var : TEMP]
               ; Sig.type_ Recursive
                   [ Type.mk (ident (name ^ "Var")) ~manifest:[%type: Var.t] ]
               ; Sig.type_ Recursive
                   [ type_decl_of_cases
                       ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
                       ~extra_cases:
                         [ Type.constructor
                             (ident "Var")
                             ~args:
                               (Pcstr_tuple
                                  [ type_var ~via_module:(refer_to_via_module name) name ])
                         ]
                       ~deriving_sexp:false
                       ~name:"view"
                       cases
                   ]
               ]
             @
             view_conversion_intf
             @
             convenient_constructors_intf
               ~keywords
               ~type_of_abt:(exposed_type_of_abt ~use_temp_directly:false ~refer_to_via_module)
               ~is_sort:true
               cases
             @
             [ subst_function_signature_item ~args:[] ])
      in
      Md.mk (ident (Some (String.capitalize name))) module_type)
  in
  let modules =
    per_defn_modl_decls
    @
    [ Md.mk (ident (Some "Subst"))
        (Mty.signature
           [ Sig.type_ Recursive
               (subst_type
                  (List.filter_map defns ~f:(fun { name; args = _; body } ->
                     match body with
                     | Sort _ -> Some name
                     | _ -> None)))
           ])
    ]
  in
  [ Str.modtype
      (Mtd.mk (ident (String.uppercase context.structure_name))
         ~typ:
           (Mty.signature
              ([%sigi: type ('a, 'b) bind = 'a * 'b]
               :: List.map modules ~f:Sig.module_
               @ (Hashtbl.to_alist context.dependencies
                  |> List.concat_map ~f:(fun (name, dependencies) ->
                    [%sigi:
                      [%%sharing_type:
                        [%t Typ.constr (lident (String.capitalize name ^ ".subst")) []]
                        * [%t Typ.constr (lident "Subst.t") []]
                      ]]
                    :: (List.filter (Set.to_list dependencies) ~f:(fun (_sort, name') ->
                      match context.compare_declaration_order name name' with
                      | Less -> true
                      | Equal | Greater -> false)
                        |> List.map ~f:(fun (sort, name') ->
                          match sort with
                          | `Direct ->
                            [%sigi:
                              [%%sharing_type:
                                [%t Typ.constr (lident (String.capitalize name ^ "." ^ name')) []]
                                * [%t Typ.constr (lident (String.capitalize name' ^ ".t")) []]
                              ]]
                          | `Var ->
                            [%sigi:
                              [%%sharing_type:
                                [%t Typ.constr (lident (String.capitalize name ^ "." ^ name' ^ "Var")) []]
                                * [%t Typ.constr (lident (String.capitalize name' ^ ".Var.t")) []]
                              ]])))))))
  ]
;;

let global_constructor_name ~name ~constructor_name =
  String.capitalize name ^ "_" ^ constructor_name
;;

let types_for_sharing (context : Context.t) name =
  Hashtbl.find_exn context.dependencies name
  |> Set.to_list
  |> List.filter ~f:(fun (_sort, name') ->
    match context.compare_declaration_order name name' with
    | Less -> true
    | Equal | Greater -> false)
  |> List.map ~f:(fun (sort, name') ->
    Str.type_ Recursive
      [ Type.mk
          (ident
             (match sort with
              | `Direct -> name'
              | `Var -> name' ^ "Var"))
          ~manifest:
            (match sort with
             | `Direct -> type_t ~via_module:false name'
             | `Var -> Typ.constr (lident "Temp.t") [])
      ])
;;

module Foo = struct
  module Variant = struct
    type _ t =
      | Simple : { args : string list } -> [ `Simple ] t
      | Open : [ `Open ] t
      | Closed : [ `Closed ] t
      | Sort : [ `Closed ] t
  end

  type 'a t =
    { name : string; cases : 'a Cases.t; variant : 'a Variant.t }

  module Packed = struct
    type 'a unpacked = 'a t
    type t = T : _ unpacked -> t
  end
end

let raise_internal_error_expr = [%expr raise (Fail [%e internal_error_message])]

open
  Walks (struct
    let use_flat_names_internally = true
    let qualify_constructors = true
    let raise_internal_error_expr = raise_internal_error_expr
  end)

(* CR wduff: Make defns a hash_queue or something else that allows lookup but preserves ordering? *)
let gen_implementation (context : Context.t) (defns : Defn.t list) : Ppxlib.Parsetree.structure =
  let refer_to_via_module = const false in
  let lang = `Sml in
  let external_abts = Queue.create () in
  let symbols = Queue.create () in
  let (simple_abts : (string * string list * [ `Simple ] Cases.t) Queue.t) = Queue.create () in
  let (open_abts : (string * [ `Open ] Cases.t) Queue.t) = Queue.create () in
  let (closed_abts : (string * [ `Closed ] Cases.t) Queue.t) = Queue.create () in
  let sorts = Queue.create () in
  List.iter defns ~f:(fun { name; args; body } ->
    match body with
    | External_simple_abt ->
      Queue.enqueue external_abts (name, args)
    | Symbol ->
      Queue.enqueue symbols name
    | Internal_abt (T (Simple, cases)) ->
      Queue.enqueue simple_abts (name, args, cases)
    | Internal_abt (T (Open, cases)) ->
      begin
        match args with
        | [] -> ()
        | _::_ ->
          (* CR wduff: Better error. *)
          raise_s [%message ""]
      end;
      Queue.enqueue open_abts (name, cases)
    | Internal_abt (T (Closed, cases)) ->
      begin
        match args with
        | [] -> ()
        | _::_ ->
          (* CR wduff: Better error. *)
          raise_s [%message ""]
      end;
      Queue.enqueue closed_abts (name, cases)
    | Sort cases ->
      begin
        match args with
        | [] -> ()
        | _::_ ->
          (* CR wduff: Better error. *)
          raise_s [%message ""]
      end;
      Queue.enqueue sorts (name, cases));
  let external_abts = Queue.to_list external_abts in
  let symbols = Queue.to_list symbols in
  let simple_abts = Queue.to_list simple_abts in
  let open_abts = Queue.to_list open_abts in
  let closed_abts = Queue.to_list closed_abts in
  let sorts = Queue.to_list sorts in
  (* CR wduff: Implement map for simple abts. *)
  let external_simple_abts_with_apply_subst =
    List.map external_abts ~f:(fun (name, args) ->
      Str.module_
        (Mb.mk
           (ident (Some (String.capitalize name)))
           (Mod.structure
              [ Str.type_ Recursive
                  [ Type.mk (ident "t")
                      ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                      ~manifest:(type_t ~via_module:true ~args:(List.map args ~f:Typ.var) name)
                  ]
              ; [%stri
                let apply_subst =
                  [%e
                    match args with
                    | [] -> [%expr fun _ acc t -> (acc, t)]
                    | _::_ ->
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
                            fun subst acc (t : [%t t1]) : ('acc * [%t t2]) ->
                              [%e
                                Exp.apply
                                  (eident (String.capitalize name ^ ".fold_map"))
                                  (* CR wduff: This argument order is unnatural for sml. *)
                                  ((Nolabel, eident "t")
                                   ::
                                   (Nolabel, eident "acc")
                                   ::
                                   List.map args ~f:(fun arg ->
                                     (* CR wduff: Special case the 1 case. *)
                                     (Nolabel,
                                      [%expr [%e eident ("apply_subst_" ^ arg)] subst])))
                              ]
                          ]
                  ]
              ]
              ; [%stri
                let subst =
                  [%e
                    (match args with
                     | [] -> [%expr fun _ t -> t]
                     | _::_ ->
                       List.fold_right args
                         ~f:(fun arg acc ->
                           Exp.fun_ Nolabel None (pvar ("subst_" ^ arg)) acc)
                         ~init:
                           [%expr
                             fun subst t ->
                               let ((), t) =
                                 [%e
                                   Exp.apply
                                     (eident (String.capitalize name ^ ".fold_map"))
                                     ((Nolabel, eident "t")
                                      ::
                                      (Nolabel, [%expr ()])
                                      ::
                                      List.map args ~f:(fun arg ->
                                        (Nolabel,
                                         [%expr
                                           fun () [%p pvar arg] ->
                                             ((), [%e eident ("subst_" ^ arg)] subst [%e eident arg])])))]
                               in
                               t])]]
              ])))
  in
  let datatype_defns =
    List.map simple_abts ~f:(fun (name, args, cases) ->
      Type.mk
        (ident name)
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
                                   ~use_temp_directly:true
                                   ~refer_to_via_module))))))))
    @
    List.map open_abts ~f:(fun (name, cases) ->
      Type.mk
        (ident (name ^ "_oper"))
        ~kind:
          (Ptype_variant
             (List.map cases ~f:(fun (constructor_name, abt) ->
                Type.constructor
                  (ident (global_constructor_name ~name ~constructor_name))
                  ~args:
                    (Pcstr_tuple
                       (Option.to_list
                          (Option.map abt
                             ~f:(internal_type_of_abt ~refer_to_via_module ~lang))))))))
    @
    List.map closed_abts ~f:(fun (name, cases) ->
      Type.mk
        (ident (name ^ "_oper"))
        ~kind:
          (Ptype_variant
             (List.map cases ~f:(fun (constructor_name, abt) ->
                Type.constructor
                  (ident (global_constructor_name ~name ~constructor_name))
                  ~args:
                    (Pcstr_tuple
                       (Option.to_list
                          (Option.map abt
                             ~f:(internal_type_of_abt ~refer_to_via_module ~lang))))))))
    @
    List.map sorts ~f:(fun (name, cases) ->
      Type.mk
        (ident (name ^ "_oper"))
        ~kind:
          (Ptype_variant
             (List.map cases ~f:(fun (constructor_name, abt) ->
                Type.constructor
                  (ident (global_constructor_name ~name ~constructor_name))
                  ~args:
                    (Pcstr_tuple
                       (Option.to_list
                          (Option.map abt
                             ~f:(internal_type_of_abt ~refer_to_via_module ~lang))))))))
  in
  let type_alias_defns =
    List.map external_abts ~f:(fun (name, args) ->
      Type.mk (ident name)
        ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
        ~manifest:
          (Typ.constr (lident (String.capitalize name ^ ".t")) (List.map args ~f:Typ.var)))
    @
    List.map symbols ~f:(fun name ->
      Type.mk (ident name)
        ~manifest:
          (Typ.constr (lident "Temp.t") []))
    @
    List.map open_abts ~f:(fun (name, _) ->
      Type.mk (ident (name ^ "_internal"))
        ~manifest:
          (Typ.constr (lident "With_subst.t") [Typ.constr (lident (name ^ "_oper")) []]))
    @
    List.map closed_abts ~f:(fun (name, _) ->
      Type.mk (ident name)
        ~manifest:
          (Typ.constr (lident "With_subst.t") [Typ.constr (lident (name ^ "_oper")) []]))
    @
    List.map sorts ~f:(fun (name, _) ->
      Type.mk (ident name)
        ~manifest:
          (Typ.constr (lident "Internal_sort.t") [Typ.constr (lident (name ^ "_oper")) []]))
  in
  let simple_abt_specific_structure_items =
    List.map external_abts ~f:(fun (name, _) ->
      [%stri
        let [%p pvar (name ^ "_apply_subst")] =
          [%e eident (String.capitalize name ^ ".apply_subst")]
      ])
    @
    (match simple_abts with
     | [] -> []
     | _::_ ->
       [ Str.value Recursive
           (List.map simple_abts ~f:(fun (name, args, cases) ->
              let (cases, used_subst) =
                apply_subst_code_for_simple_cases
                  ~subst:[%expr subst]
                  cases
              in
              let subst_pat =
                match used_subst with
                | `Used_subst -> pvar "subst"
                | `Ignored_subst -> pvar "_"
              in
              (Vb.mk
                 (pvar (name ^ "_apply_subst"))
                 (List.fold_right args
                    ~f:(fun arg acc ->
                      Exp.fun_ Nolabel None (pvar ("apply_subst_" ^ arg)) acc)
                    ~init:
                      [%expr fun [%p subst_pat] [%p pvar name] ->
                        [%e Exp.match_ (eident name) cases]]))))
       ])
  in
  let open_abt_specific_structure_items =
    match open_abts with
    | [] -> []
    | _::_ ->
      let open_abt_exposed_types_defn =
        List.map open_abts ~f:(fun (name, cases) ->
          Type.mk (ident name)
            ~kind:
              (Ptype_variant
                 (List.map cases ~f:(fun (constructor_name, abt) ->
                    Type.constructor
                      (* CR wduff: This could lead to name conflicts between open abts. *)
                      (ident (String.capitalize constructor_name))
                      ~args:
                        (Pcstr_tuple
                           (Option.to_list
                              (Option.map abt
                                 ~f:(exposed_type_of_abt
                                       ~use_temp_directly:true
                                       ~refer_to_via_module))))))))
        |> Str.type_ Recursive
      in
      let open_abt_intos_defn =
        List.map open_abts ~f:(fun (name, cases) ->
          Vb.mk
            (pvar (name ^ "_into"))
            (Exp.fun_ Nolabel None
               (pvar name)
               (Exp.let_ Nonrecursive
                  [ Vb.mk
                      (Pat.tuple [ pvar "vars"; pvar name ])
                      (Exp.match_
                         (eident name)
                         (into_code_for_open_cases
                            ~name_of_walked_value:name
                            cases))
                  ]
                  (Exp.tuple
                     [ eident "vars"
                     ; Exp.tuple [ eident "Subst.ident"; eident name]
                     ]))))
        |> Str.value Recursive
      in
      let open_abt_outs_defn =
        List.map open_abts ~f:(fun (name, cases) ->
          Vb.mk
            (pvar (name ^ "_out"))
            (Exp.fun_ Nolabel None
               (Pat.tuple [ pvar "subst"; pvar name ])
               (Exp.match_
                  (eident name)
                  (out_code_for_open_cases
                     ~name_of_walked_value:name
                     cases))))
        |> Str.value Recursive
      in
      [ open_abt_exposed_types_defn
      ; open_abt_intos_defn
      ; open_abt_outs_defn
      ]
  in
  let modules_without_subst =
    List.map simple_abts ~f:(fun (name, args, _) ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.structure
              (types_for_sharing context name
               @
               [ Str.type_ Recursive
                   [ Type.mk
                       (ident "t")
                       ~manifest:(Typ.constr (lident name) [])
                       ~kind:(Ptype_variant [])
                   ]
               ; Str.type_ Recursive
                   [ Type.mk
                       (ident name)
                       ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                       ~manifest:(Typ.constr (lident "t") (List.map args ~f:Typ.var))
                   ]
               ]))))
    @
    List.map open_abts ~f:(fun (name, _) ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.structure
              (types_for_sharing context name
               @ [ Str.type_ Recursive
                     [ Type.mk
                         (ident "t")
                         ~manifest:(Typ.constr (lident name) [])
                         ~kind:(Ptype_variant [])
                     ]
                 ; Str.type_ Recursive
                     [ Type.mk (ident name) ~manifest:(Typ.constr (lident "t") []) ]
                 ]))))
    @
    List.map closed_abts ~f:(fun (name, cases) ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.structure
              (types_for_sharing context name
               @ [ Str.type_ Recursive
                     [ Type.mk (ident "oper") ~manifest:(Typ.constr (lident (name ^ "_oper")) []) ]
                 ; Str.type_ Recursive
                     [ Type.mk (ident "t") ~manifest:(Typ.constr (lident name) []) ]
                 ; Str.type_ Recursive
                     [ Type.mk (ident name) ~manifest:(Typ.constr (lident "t") []) ]
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
                                                    ~use_temp_directly:true
                                                    ~refer_to_via_module)))))))
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
                      | `Ignored_subst -> [%pat? _]
                    in
                    [%stri
                      let out ([%p subst_pat], oper) : view =
                        [%e Exp.match_ [%expr (oper : oper)] oper_cases_expr]
                    ])
                 ]
               @ convenient_constructors_impl ~keywords ~is_sort:false cases))))
    @
    List.map symbols ~f:(fun name ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.ident (lident "Temp"))))
    @
    List.map sorts ~f:(fun (name, cases) ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.structure
              (types_for_sharing context name
               @
               [ Str.type_ Recursive
                   [ Type.mk (ident "oper") ~manifest:(Typ.constr (lident (name ^ "_oper")) []) ]
               ; Str.type_ Recursive
                   [ Type.mk (ident "t") ~manifest:(Typ.constr (lident name) []) ]
               ; Str.type_ Recursive
                   [ Type.mk (ident name) ~manifest:(Typ.constr (lident "t") []) ]
               ; Str.module_ (Mb.mk (ident (Some "Var")) (Mod.ident (lident "Temp")))
               ; Str.type_ Recursive
                   [ Type.mk (ident (name ^ "Var")) ~manifest:(Typ.constr (lident "Var.t") []) ]
               ; Str.type_ Recursive
                   [ Type.mk (ident "view")
                       ~kind:
                         (Ptype_variant
                            (Type.constructor
                               (ident "Var")
                               ~args:(Pcstr_tuple [type_var ~via_module:false name])
                             :: List.map cases ~f:(fun (constructor_name, abt) ->
                               Type.constructor
                                 (ident constructor_name)
                                 ~args:
                                   (Pcstr_tuple
                                      (Option.to_list
                                         (Option.map abt
                                            ~f:(exposed_type_of_abt
                                                  ~use_temp_directly:true
                                                  ~refer_to_via_module)))))))
                   ]
               ; [%stri
                 let into (view : view) : t =
                   [%e
                     Exp.match_
                       [%expr view]
                       ({ pc_lhs = [%pat? Var var]
                        ; pc_guard = None
                        ; pc_rhs = [%expr Internal_sort.Var (Internal_var.Free_var var)]
                        }
                        :: List.map
                             (into_code_for_closed_cases
                                ~name_of_walked_value:name
                                cases)
                             ~f:(fun { pc_lhs; pc_guard; pc_rhs } ->
                               { pc_lhs
                               ; pc_guard
                               ; pc_rhs = [%expr Internal_sort.Oper (Subst.ident, [%e pc_rhs])]
                               }))
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
                    | `Ignored_subst -> [%pat? _]
                  in
                  [%stri
                    let out (t : t) : view =
                      match t with
                      | Internal_sort.Var (Internal_var.Bound_var _) -> [%e raise_internal_error_expr]
                      | Internal_sort.Var (Internal_var.Free_var var) -> Var var
                      | Internal_sort.Oper ([%p subst_pat], oper) ->
                        [%e Exp.match_ [%expr oper] oper_cases_expr]
                  ])
               ]
               @
               convenient_constructors_impl ~keywords ~is_sort:true cases))))
  in
  let external_subst_functions =
    List.map external_abts ~f:(fun (name, _args) ->
      [%stri let [%p pvar (name ^ "_subst")] = [%e eident (String.capitalize name ^ ".subst")]])
  in
  (* CR wduff: rename this. *)
  let of_foo (type a) ({ name; cases; variant } : a Foo.t) =
    let (cases, used_sub) =
      subst_code_for_cases
        ~name_of_walked_value:name
        ~sub:[ (Nolabel, "subst") ]
        cases
    in
    let subst_pat =
      match used_sub with
      | `Used_sub -> pvar "subst"
      | `Ignored_sub -> pvar "_"
    in
    let body =
      match variant with
      | Simple { args } ->
        List.fold_right args
          ~f:(fun arg acc ->
            [%expr fun [%p pvar ("subst_" ^ arg)] -> [%e acc]])
          ~init:
            [%expr fun [%p subst_pat] [%p pvar name] ->
              [%e Exp.match_ (eident name) cases]]
      | Open ->
        [%expr fun [%p subst_pat] [%p pvar name] ->
          [%e Exp.match_ (eident name) cases]]
      | Closed ->
        [%expr fun [%p subst_pat] [%p pvar name] ->
          let view =
            [%e
              Exp.match_
                [%expr [%e eident (String.capitalize name ^ ".out")] [%e eident name]]
                cases
            ]
          in
          [%e eident (String.capitalize name ^ ".into")] view
        ]
      | Sort ->
        [%expr fun [%p subst_pat] [%p pvar name] ->
          [%e
            Exp.match_
              [%expr [%e eident (String.capitalize name ^ ".out")] [%e eident name]]
              (Exp.case
                 (Pat.construct
                    (lident (String.capitalize name ^ "." ^ "Var"))
                    (Some [%pat? var]))
                 (Exp.match_
                    [%expr subst]
                    (Exp.case
                       (Pat.construct
                          (lident ("Subst." ^ String.capitalize name))
                          (Some [%pat? ([%p pvar ("subst_" ^ name)], subst_var)]))
                       (Exp.match_
                          [%expr Temp.eq (subst_var, var)]
                          [ Exp.case [%pat? true] (eident ("subst_" ^ name))
                          ; Exp.case [%pat? false] (eident name)
                          ])
                     ::
                     (match sorts with
                      | [_] ->
                        (* If there is exactly one sort, we drop this case to avoid a redundant
                           match warning. *)
                        []
                      | _ ->
                        [ Exp.case [%pat? _] (eident name) ])))
               ::
               (List.map cases ~f:(fun { pc_lhs; pc_guard; pc_rhs } ->
                  { pc_lhs
                  ; pc_guard
                  ; pc_rhs =
                      [%expr
                        let view = [%e pc_rhs] in
                        [%e eident (String.capitalize name ^ ".into")] view]
                  })))
          ]]
    in
    Vb.mk (pvar (name ^ "_subst")) body
  in
  let depends dependent ~on =
    Set.mem (Hashtbl.find_exn context.dependencies dependent) on
  in
  let sccs : Foo.Packed.t list list =
    (* CR wduff: If this will require polymorphic recursion, complain in the type checker. *)
    (* CR wduff: Just create the graph from the start instead of using a map for dependencies
       everywhere else? *)
    let module Dependence = Graph.Persistent.Digraph.ConcreteBidirectional (String) in
    let module SCC = Graph.Components.Make (Dependence) in
    (* CR wduff: The copious transformations of the data are gross. *)
    let simple_abts =
      List.map simple_abts ~f:(fun (name, args, cases) ->
        (name, (Foo.Packed.T { name; cases; variant = Simple { args } })))
      |> String.Map.of_alist_exn
    in
    let open_abts =
      List.map open_abts ~f:(fun (name, cases) ->
        (name, (Foo.Packed.T { name; cases; variant = Open })))
      |> String.Map.of_alist_exn
    in
    let closed_abts =
      List.map closed_abts ~f:(fun (name, cases) ->
        (name, (Foo.Packed.T { name; cases; variant = Closed })))
      |> String.Map.of_alist_exn
    in
    let sorts =
      List.map sorts ~f:(fun (name, cases) ->
        (name, (Foo.Packed.T { name; cases; variant = Sort })))
      |> String.Map.of_alist_exn
    in
    let foos =
      let merge =
        Map.merge ~f:(fun ~key:_ -> function
          | `Left x | `Right x -> Some x
          (* CR wduff: Can this happen? If so we need a better error message. *)
          | `Both _ -> assert false)
      in
      merge
        (merge simple_abts open_abts)
        (merge closed_abts sorts)
    in
    let should_track name =
      (* We assume that if it isn't in [foos] that's because it is a symbol or external abt. *)
      Map.mem foos name
    in
    Hashtbl.fold context.dependencies ~init:Dependence.empty
      ~f:(fun ~key:name1 ~data dep_graph ->
        match should_track name1 with
        | false -> dep_graph
        | true ->
          let dep_graph = Dependence.add_vertex dep_graph name1 in
          Set.fold data ~init:dep_graph ~f:(fun dep_graph (how, name2) ->
            match how with
            | `Var -> dep_graph
            | `Direct ->
              match Map.find foos name2 with
              | None -> dep_graph
              | Some _ ->
                match should_track name2 with
                | false -> dep_graph
                | true ->
                  Dependence.add_edge dep_graph name1 name2))
    |> SCC.scc_list
    |> List.map ~f:(List.map ~f:(Map.find_exn foos))
  in
  let internal_subst_functions =
    List.map sccs ~f:(fun scc ->
      match scc with
      | [] -> assert false
      (* CR wduff: rename this. *)
      | [T ({ name; cases = _; variant = _ } as foo)] ->
        let (rec_flag : rec_flag) =
          match depends name ~on:(`Direct, name) with
          | true -> Recursive
          | false -> Nonrecursive
        in
        Str.value rec_flag [ of_foo foo ]
      | _::_::_ ->
        Str.value Recursive
          (List.map scc ~f:(fun (T foo) ->
             of_foo foo)))
  in
  let modules_with_subst =
    List.concat
      [ List.map ~f:fst external_abts
      ; List.map ~f:Tuple3.get1 simple_abts
      ; List.map ~f:fst open_abts
      ; List.map ~f:fst closed_abts
      ; List.map ~f:fst sorts
      ]
    |> List.map ~f:(fun name ->
      Str.module_
        (Mb.mk (ident (Some (String.capitalize name)))
           (Mod.structure
              [ [%stri type subst = Subst.t]
              ; Str.include_
                  { pincl_mod = Mod.ident (lident (String.capitalize name))
                  ; pincl_attributes = []
                  ; pincl_loc = loc
                  }
              ; Str.value Nonrecursive
                  [ Vb.mk (pvar "subst") (eident (name ^ "_subst")) ]
              ])))
  in
  [ Str.module_
      (Mb.mk (ident (Some (String.capitalize context.structure_name)))
         (List.fold (List.rev external_abts)
            ~f:(fun acc (name, args) ->
              Mod.functor_
                (Named
                   (ident (Some (String.capitalize name)),
                    (Mty.signature
                       [ Sig.type_ Recursive
                           [ Type.mk (ident "t")
                               ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                           ]
                       (* CR wduff: This argument order is unnatural for sml. *)
                       ; Sig.value
                           (Val.mk (ident "fold_map")
                              (Typ.arrow Nolabel
                                 (Typ.constr
                                    (lident "t")
                                    (List.map args ~f:(fun arg -> Typ.var (arg ^ "1"))))
                                 (Typ.arrow Nolabel
                                    (Typ.var "acc")
                                    (List.fold_right args
                                       ~f:(fun arg acc ->
                                         Typ.arrow Nolabel
                                           (Typ.arrow Nolabel
                                              (Typ.var "acc")
                                              (Typ.arrow Nolabel
                                                 (Typ.var (arg ^ "1"))
                                                 (Typ.tuple
                                                    [ Typ.var "acc"
                                                    ; Typ.var (arg ^ "2")
                                                    ])))
                                           acc)
                                       ~init:
                                         (Typ.tuple
                                            [ Typ.var "acc"
                                            ; Typ.constr
                                                (lident "t")
                                                (List.map args ~f:(fun arg -> Typ.var (arg ^ "2")))
                                            ])))))
                       ])))
                acc)
            ~init:
              (Mod.constraint_
                 (Mod.structure
                    ([ [%stri type ('a, 'b) bind = 'a * 'b] ]
                     @
                     external_simple_abts_with_apply_subst
                     @
                     [ Str.type_ Recursive (datatype_defns @ type_alias_defns) ]
                     @
                     simple_abt_specific_structure_items
                     @
                     open_abt_specific_structure_items
                     @
                     modules_without_subst
                     @
                     [ Str.module_
                         (Mb.mk (ident (Some "Subst"))
                            (Mod.structure
                               [ Str.type_ Recursive (subst_type (List.map ~f:fst sorts)) ]))
                     ]
                     @
                     external_subst_functions
                     @
                     internal_subst_functions
                     @
                     modules_with_subst))
                 (Mty.with_
                    (Mty.ident (lident (String.uppercase context.structure_name)))
                    (List.map external_abts ~f:(fun (name, args) ->
                       Pwith_type
                         (lident (String.capitalize name ^ ".t"),
                          Type.mk (ident (String.capitalize name ^ ".t"))
                            ~params:(List.map args ~f:(fun arg -> (Typ.var arg, Invariant)))
                            ~manifest:
                              (Typ.constr
                                 (lident (String.capitalize name ^ ".t"))
                                 (List.map args ~f:Typ.var)))))))))
  ]
;;

let rec dependencies_of_abt : type k. k Abt.t -> Dependency.Set.t = function
  | Arg_use _name ->
    Dependency.Set.empty
  | Builtin_abt_use ((_ : Builtin_abt.t), args) ->
    Dependency.Set.union_list
      (List.map args ~f:dependencies_of_abt)
  | Simple_abt_use (name, args) ->
    Dependency.Set.union_list
      (Dependency.Set.singleton (`Direct, name)
       :: List.map args ~f:dependencies_of_abt)
  | Open_abt_use name ->
    Dependency.Set.singleton (`Direct, name)
  | Closed_abt_use name ->
    Dependency.Set.singleton (`Direct, name)
  | Symbol_use name ->
    Dependency.Set.singleton (`Direct, name)
  | Sort_use name ->
    Dependency.Set.singleton (`Direct, name)
  | Prod abts ->
    List.map abts ~f:dependencies_of_abt
    |> Dependency.Set.union_list
  | Sort_binding name ->
    Dependency.Set.singleton (`Var, name)
  | Symbol_binding name ->
    Dependency.Set.singleton (`Var, name)
  | Bind (lhs, rhs) ->
    Set.union (dependencies_of_abt lhs) (dependencies_of_abt rhs)
;;

let gen_ast ~structure_name (defns : Defn.t list) =
  let compare_declaration_order =
    let index_by_name =
      List.mapi ~f:(fun i name -> (name, i)) (List.map ~f:Defn.name defns @ [ "sort"; "subst" ])
      |> String.Table.of_alist_exn
    in
    (fun name1 name2 ->
       Int.compare
         (Hashtbl.find_exn index_by_name name1)
         (Hashtbl.find_exn index_by_name name2)
       |> Ordering.of_int)
  in
  let dependencies =
    List.filter_map defns ~f:(fun { name; args = _; body } ->
      let dependencies =
        match body with
        | Symbol -> None
        | External_simple_abt -> Some (Dependency.Set.empty)
        | Internal_abt (T (_kind, cases)) ->
          List.map cases ~f:(fun (_, abt) ->
            match abt with
            | None -> Dependency.Set.empty
            | Some abt -> dependencies_of_abt abt)
          |> Dependency.Set.union_list
          |> Some
        | Sort cases ->
          List.map cases ~f:(fun (_, abt) ->
            match abt with
            | None -> Dependency.Set.empty
            | Some abt -> dependencies_of_abt abt)
          |> Dependency.Set.union_list
          |> Some
      in
      Option.map dependencies ~f:(fun dependencies ->
        (name, dependencies)))
    |> String.Table.of_alist_exn
  in
  let (context : Context.t) =
    { structure_name
    ; compare_declaration_order
    ; dependencies
    }
  in
  (gen_interface context defns, gen_implementation context defns)
;;
