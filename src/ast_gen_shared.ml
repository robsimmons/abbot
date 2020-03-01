open! Core
open Ppxlib
open Ast_helper
open Typed

let rec unzip3 = function
  | [] -> ([], [], [])
  | (x, y, z) :: rest ->
    let (xs, ys, zs) = unzip3 rest in
    (x :: xs, y :: ys, z :: zs)

(* CR wduff: Ensure there is no possibility of unused variable warnings. *)

let loc = Location.none

let lident string =
  match String.split ~on:'.' string with
  | [] -> raise_s [%message "Abbot bug: empty lident."]
  | var::fields ->
    { loc
    ; txt =
        List.fold fields ~init:(Lident var) ~f:(fun acc field ->
          Ldot (acc, field))
    }
;;

let eident string =
  Exp.ident (lident string)
;;

let ident string =
  { txt = string; loc }
;;

let pvar string =
  Pat.var (ident string)
;;

let type_t ~via_module ?(args = []) string =
  let lident_string =
    match via_module with
    | true -> String.capitalize string ^ ".t"
    | false -> string
  in
  Typ.constr (lident lident_string) args
;;

let type_internal ~via_module ?(args = []) string =
  let lident_string =
    match via_module with
    | true -> String.capitalize string ^ ".internal"
    | false -> string ^ "_internal"
  in
  Typ.constr (lident lident_string) args
;;

let type_var ~via_module string =
  let lident_string =
    match via_module with
    | true -> String.capitalize string ^ ".Var.t"
    | false -> string ^ "Var"
  in
  Typ.constr (lident lident_string) []
;;

let rec internal_type_of_abt
  : type a. refer_to_via_module:(string -> bool) -> a Abt.t -> core_type =
  fun ~refer_to_via_module abt ->
    match abt with
    | Arg_use name ->
      Typ.var name
    | Builtin_abt_use (builtin_abt, args) ->
      Typ.constr
        (lident (Builtin_abt.module_name builtin_abt ^ ".t"))
        (List.map args ~f:(internal_type_of_abt ~refer_to_via_module))
    | Simple_abt_use (name, args) ->
      type_t
        ~via_module:(refer_to_via_module name)
        ~args:(List.map args ~f:(internal_type_of_abt ~refer_to_via_module))
        name
    | Closed_abt_use name | Sort_use name ->
      type_t ~via_module:(refer_to_via_module name) name
    | Symbol_use (_ : string) ->
      Typ.constr (lident "Internal_var.t") []
    | Open_abt_use name ->
      type_internal ~via_module:(refer_to_via_module name) name
    | Prod abts ->
      Typ.tuple (List.map abts ~f:(internal_type_of_abt ~refer_to_via_module))
    | Symbol_binding _ ->
      [%type: string compare_ignore]
    | Sort_binding _ ->
      [%type: string compare_ignore]
    | Bind (lhs, rhs) ->
      Typ.constr (lident "bind")
        [ internal_type_of_abt ~refer_to_via_module lhs
        ; internal_type_of_abt ~refer_to_via_module rhs
        ]
;;

let rec exposed_type_of_abt
  : type a. use_temp_directly:bool -> refer_to_via_module:(string -> bool) -> a Abt.t -> core_type =
  fun ~use_temp_directly ~refer_to_via_module abt ->
    match abt with
    | Arg_use name ->
      Typ.var name
    | Open_abt_use name ->
      type_t ~via_module:(refer_to_via_module name) name
    | Closed_abt_use name | Symbol_use name | Sort_use name ->
      type_t ~via_module:(refer_to_via_module name) name
    | Builtin_abt_use (builtin_abt, args) ->
      Typ.constr
        (lident (Builtin_abt.core_type builtin_abt))
        (List.map args ~f:(exposed_type_of_abt ~use_temp_directly ~refer_to_via_module))
    | Simple_abt_use (name, args) ->
      type_t
        ~via_module:(refer_to_via_module name)
        ~args:(List.map args ~f:(exposed_type_of_abt ~use_temp_directly ~refer_to_via_module))
        name
    | Prod abts ->
      Typ.tuple (List.map abts ~f:(exposed_type_of_abt ~use_temp_directly ~refer_to_via_module))
    | Symbol_binding name ->
      begin
        match use_temp_directly with
        | true -> Typ.constr (lident "Temp.t") []
        | false ->
          type_t ~via_module:(refer_to_via_module name) name
      end
    | Sort_binding name ->
      begin
        match use_temp_directly with
        | true -> Typ.constr (lident "Temp.t") []
        | false ->
          type_var ~via_module:(refer_to_via_module name) name
      end
    | Bind (lhs, rhs) ->
      Typ.constr (lident "bind")
        [ exposed_type_of_abt ~use_temp_directly ~refer_to_via_module lhs
        ; exposed_type_of_abt ~use_temp_directly ~refer_to_via_module rhs
        ]
;;

let deriving_sexp_attribute =
  Attr.mk (ident "deriving") (PStr [ Str.eval (eident "sexp_of") ])
;;

(* CR wduff: Simpify this away. *)
let type_decl_of_cases ~type_of_abt ?(extra_cases = []) ~deriving_sexp ~name cases =
  Type.mk
    (ident name)
    ~kind:
      (Ptype_variant
         (extra_cases
          @ List.map cases ~f:(fun (constructor_name, abt) ->
            Type.constructor
              (ident constructor_name)
              ~args:(Pcstr_tuple (Option.to_list (Option.map abt ~f:type_of_abt))))))
    ~attrs:
      (match deriving_sexp with
       | true -> [deriving_sexp_attribute]
       | false -> [])
;;

let view_conversion_intf =
  [ [%sigi: val into : view -> t]
  ; [%sigi: val out : t -> view]
  ]
;;

let convenient_constructors_intf ~keywords ~type_of_abt ~is_sort cases =
  let opers =
    List.map cases ~f:(fun (constructor_name, abt_opt) ->
      let convenient_constructor_name = String.lowercase constructor_name in
      let convenient_constructor_name =
        match Set.mem keywords convenient_constructor_name with
        | true -> convenient_constructor_name ^ "_"
        | false -> convenient_constructor_name
      in
      let name = ident convenient_constructor_name in
      match abt_opt with
      | None ->
        Sig.value (Val.mk name [%type: unit -> t])
      | Some abt ->
        Sig.value (Val.mk name [%type: [%t type_of_abt abt] -> t]))
  in
  match is_sort with
  | false -> opers
  | true ->
    [%sigi: val var : Var.t -> t] :: opers
;;

let convenient_constructors_impl ~keywords ~is_sort cases =
  let opers =
    List.map cases ~f:(fun (constructor_name, abt_opt) ->
      let convenient_constructor_name = String.lowercase constructor_name in
      let convenient_constructor_name =
        match Set.mem keywords convenient_constructor_name with
        | true -> convenient_constructor_name ^ "_"
        | false -> convenient_constructor_name
      in
      let pat = Pat.var (ident convenient_constructor_name) in
      match abt_opt with
      | None ->
        Str.value Nonrecursive
          [ Vb.mk
              pat
              (Exp.fun_ Nolabel None
                 (Pat.tuple [])
                 (Exp.apply
                    (Exp.ident (lident "into"))
                    [ (Nolabel, Exp.ident (lident constructor_name)) ]))
          ]
      | Some _ ->
        Str.value Nonrecursive
          [ Vb.mk
              pat
              (Exp.fun_ Nolabel None
                 (Pat.var (ident "arg"))
                 (Exp.apply
                    (Exp.ident (lident "into"))
                    [ (Nolabel,
                       Exp.apply
                         (Exp.ident (lident constructor_name))
                         [ (Nolabel, (Exp.ident (lident "arg"))) ])
                    ]))
          ])
  in
  match is_sort with
  | false -> opers
  | true ->
    [%stri let var arg = into (Var arg)] :: opers
;;

module Uniquifier : sig
  type t

  val create : unit -> t

  val uniquify : t -> string -> string
end = struct
  type t = int String.Table.t

  let create () = String.Table.create ()

  (* CR wduff: What if the name already ends in an int? *)
  let uniquify t name =
    let int = Hashtbl.find_or_add t name ~default:(fun () -> 1) in
    Hashtbl.set t ~key:name ~data:(int + 1);
    sprintf "%s%d" name int
end

(* CR wduff: Can some of these functions be merged now that we have a GADT? Does that actually make
   the code better? *)

let rec apply_renaming_code_for_simple_abt
          ~refer_to_simple_and_open_abts_via_module
          uniquifier
          renaming
          acc
          (abt : [ `Simple ] Abt.t)
  =
  match abt with
  | Arg_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     Exp.apply
       (eident ("apply_renaming_" ^ name))
       [ (Nolabel, renaming)
       ; (Nolabel, acc)
       ; (Nolabel, (eident name'))
       ])
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     Exp.apply
       (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
       (List.map args ~f:(fun arg ->
          let (pat, expr) =
            apply_renaming_code_for_simple_abt
              ~refer_to_simple_and_open_abts_via_module
              (Uniquifier.create ())
              (eident "renaming")
              (eident "acc")
              arg
          in
          (Nolabel,
           Exp.fun_ Nolabel None
             (Pat.var (ident "renaming"))
             (Exp.fun_ Nolabel None
                (Pat.var (ident "acc"))
                (Exp.fun_ Nolabel None pat expr))))
        @
        [ (Nolabel, renaming)
        ; (Nolabel, acc)
        ; (Nolabel, eident name')
        ]))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     Exp.apply
       (eident
          (match refer_to_simple_and_open_abts_via_module with
           | true -> String.capitalize name ^ ".apply_renaming"
           | false -> name ^ "_apply_renaming"))
       (List.map args ~f:(fun arg ->
          let (pat, expr) =
            apply_renaming_code_for_simple_abt
              ~refer_to_simple_and_open_abts_via_module
              (Uniquifier.create ())
              (eident "renaming")
              (eident "acc")
              arg
          in
          (Nolabel,
           Exp.fun_ Nolabel None
             (Pat.var (ident "renaming"))
             (Exp.fun_ Nolabel None
                (Pat.var (ident "acc"))
                (Exp.fun_ Nolabel None pat expr))))
        @
        [ (Nolabel, renaming)
        ; (Nolabel, acc)
        ; (Nolabel, eident name')
        ]))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     [%expr
       ([%e acc],
        With_renaming.apply_renaming
          [%e renaming]
          [%e eident name'])
     ])
  | Symbol_use _ -> failwith "unimpl"
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name,
     [%expr
       ([%e acc], Internal_sort.apply_renaming renaming [%e eident name])
     ])
  | Prod abts ->
    let rec foo i acc abts =
      match abts with
      | [] ->
        ([],
         Exp.tuple
           [ eident "acc"
           ; Exp.tuple (List.init i ~f:(fun i -> eident (sprintf "result_%d" i)))
           ])
      | abt :: abts ->
        let (pat, expr) =
          apply_renaming_code_for_simple_abt
            ~refer_to_simple_and_open_abts_via_module
            uniquifier
            renaming
            acc
            abt
        in
        let (pats, expr') = foo (i + 1) (eident "acc") abts in
        (pat :: pats,
         [%expr let (acc, [%p Pat.var (ident (sprintf "result_%d" i))]) = [%e expr] in [%e expr']])
    in
    let (pats, expr) = foo 0 acc abts in
    (Pat.tuple pats, expr)
;;

let rec apply_renaming_code_for_closed_abt
          ~refer_to_simple_and_open_abts_via_module
          uniquifier
          renaming
          (abt : [ `Closed ] Abt.t)
  =
  match abt with
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   apply_renaming_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     (eident "renaming")
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, renaming)
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident
                 (match refer_to_simple_and_open_abts_via_module with
                  | true -> String.capitalize name ^ ".apply_renaming"
                  | false -> name ^ "_apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   apply_renaming_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     (eident "renaming")
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, renaming)
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     [%expr With_renaming.apply_renaming [%e renaming] [%e eident name']])
  | Symbol_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, Exp.apply (eident "Renaming.apply") [ (Nolabel, eident name) ])
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, [%expr Internal_sort.apply_renaming renaming [%e eident name]])
  | Prod abts ->
    let (pats, exprs) =
      List.map abts ~f:(apply_renaming_code_for_closed_abt ~refer_to_simple_and_open_abts_via_module uniquifier renaming)
      |> List.unzip
    in
    (Pat.tuple pats, Exp.tuple exprs)
  | Bind (_lhs, _rhs) ->
    failwith "unimpl"
;;

let rec into_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier (abt : [ `Open ] Abt.t) =
  match abt with
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     `Expr
       (Exp.apply
          (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
          (List.map args ~f:(fun arg ->
             let (pat, expr) =
               into_code_for_open_abt
                 ~refer_to_simple_and_open_abts_via_module
                 (Uniquifier.create ())
                 arg
             in
             (Nolabel,
              Exp.fun_ Nolabel None
                (Pat.var (ident "renaming"))
                (Exp.fun_ Nolabel None
                   (Pat.var (ident "acc"))
                   (Exp.fun_ Nolabel None pat
                      (match expr with
                       | `Pair (vars_expr, abt_expr) ->
                         [%expr ([%e vars_expr] @ acc, [%e abt_expr])]
                       | `Expr expr ->
                         [%expr
                           let (vars, [%p Pat.var (ident name')]) = [%e expr] in
                           (vars @ acc, [%e eident name'])
                         ])))))
           @
           [ (Nolabel, eident "Renaming.ident")
           ; (Nolabel, Exp.construct (lident "[]") None)
           ; (Nolabel, eident name')
           ])))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     `Expr
       (Exp.apply
          (eident
             (match refer_to_simple_and_open_abts_via_module with
              | true -> String.capitalize name ^ ".apply_renaming"
              | false -> name ^ "_apply_renaming"))
          (List.map args ~f:(fun arg ->
             let (pat, expr) =
               into_code_for_open_abt
                 ~refer_to_simple_and_open_abts_via_module
                 (Uniquifier.create ())
                 arg
             in
             (Nolabel,
              Exp.fun_ Nolabel None
                (Pat.var (ident "renaming"))
                (Exp.fun_ Nolabel None
                   (Pat.var (ident "acc"))
                   (Exp.fun_ Nolabel None pat
                      (match expr with
                       | `Pair (vars_expr, abt_expr) ->
                         [%expr ([%e vars_expr] @ acc, [%e abt_expr])]
                       | `Expr expr ->
                         [%expr
                           let (vars, [%p Pat.var (ident name')]) = [%e expr] in
                           (vars @ acc, [%e eident name'])
                         ])))))
           @
           [ (Nolabel, eident "Renaming.ident")
           ; (Nolabel, Exp.construct (lident "[]") None)
           ; (Nolabel, eident name')
           ])))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name', `Pair ([%expr []], eident name'))
  | Open_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     `Expr
       [%expr
         [%e
           match refer_to_simple_and_open_abts_via_module with
           | true -> eident (String.capitalize name ^ ".into")
           | false -> eident (name ^ "_into")]
           [%e eident name']])
  | Symbol_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, `Pair ([%expr []], [%expr Internal_var.Free_var [%e eident name]]))
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, `Pair ([%expr []], eident name))
  | Prod abts ->
    let (pats, exprs) =
      List.map abts ~f:(into_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier)
      |> List.unzip
    in
    (* CR wduff: The names in here need to be uniquified. *)
    let (lets, vars_exprs, abt_exprs) =
      List.mapi exprs ~f:(fun i expr ->
        match expr with
        | `Pair (vars_expr, abt_expr) ->
          (None, vars_expr, abt_expr)
        | `Expr expr ->
          let vars_var = sprintf "vars_%d" i in
           (* CR wduff: Is "internal" the right name? Why? *)
          let abt_var = sprintf "internal_%d" i in
          let let_pat = [%pat? ([%p pvar vars_var], [%p pvar abt_var])] in
          let let_expr = expr in
          (Some (let_pat, let_expr), eident vars_var, eident abt_var))
      |> unzip3
    in
    let lets = List.filter_opt lets in
    let vars_expr =
      List.fold_right vars_exprs
         ~init:[%expr []]
         ~f:(fun vars_expr acc ->
           [%expr [%e vars_expr] @ [%e acc] ])
    in
    let abt_expr = Exp.tuple abt_exprs in
    (Pat.tuple pats,
     (match lets with
      | [] ->
        `Pair (vars_expr, abt_expr)
      | _::_ ->
        `Expr
          (List.fold_right lets
             ~init:[%expr ([%e vars_expr], [%e abt_expr])]
             ~f:(fun (let_pat, let_expr) acc ->
               [%expr let [%p let_pat] = [%e let_expr] in [%e acc]]))))
  | Symbol_binding name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name', `Pair ([%expr [[%e eident name']]], [%expr Temp.name [%e eident name']]))
  | Sort_binding sort ->
    let name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
    (pvar name, `Pair ([%expr [[%e eident name]]], [%expr Temp.name [%e eident name]]))
;;

let rec into_code_for_closed_abt ~refer_to_simple_and_open_abts_via_module uniquifier (abt : [ `Closed ] Abt.t) =
  match abt with
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   into_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, eident "Renaming.ident")
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident
                 (match refer_to_simple_and_open_abts_via_module with
                  | true -> String.capitalize name ^ ".apply_renaming"
                  | false -> name ^ "_apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   into_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, eident "Renaming.ident")
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name', eident name')
  | Symbol_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, Exp.construct (lident "Internal_var.Free_var") (Some (eident name)))
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, eident name)
  | Prod abts ->
    let (pats, exprs) =
      List.map abts ~f:(into_code_for_closed_abt ~refer_to_simple_and_open_abts_via_module uniquifier)
      |> List.unzip
    in
    (Pat.tuple pats, Exp.tuple exprs)
  | Bind (lhs, rhs) ->
    let (lhs_pat, lhs_expr) =
      into_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier lhs
    in
    let (rhs_pat, rhs_expr) =
      apply_renaming_code_for_closed_abt
        ~refer_to_simple_and_open_abts_via_module
        uniquifier
        [%expr renaming]
        rhs
    in
    ([%pat? ([%p lhs_pat], [%p rhs_pat])],
     (match lhs_expr with
      | `Pair (lhs_vars_expr, lhs_abt_expr) ->
        [%expr
          let renaming = Renaming.bind' [%e lhs_vars_expr] in
          ([%e lhs_abt_expr], [%e rhs_expr])
        ]
      | `Expr lhs_expr ->
        [%expr
          let (vars, lhs) = [%e lhs_expr] in
          let renaming = Renaming.bind' vars in
          (lhs, [%e rhs_expr])
        ]))
;;

let rec out_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier renaming (abt : [ `Open ] Abt.t) =
  match abt with
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     `Expr
       (Exp.apply
          (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
          (List.map args ~f:(fun arg ->
             let (pat, expr) =
               out_code_for_open_abt
                 ~refer_to_simple_and_open_abts_via_module
                 (Uniquifier.create ())
                 (eident "renaming")
                 arg
             in
             (Nolabel,
              Exp.fun_ Nolabel None
                (Pat.var (ident "renaming"))
                (Exp.fun_ Nolabel None
                   (Pat.var (ident "acc"))
                   (Exp.fun_ Nolabel None pat
                      (match expr with
                       | `Pair (vars_expr, abt_expr) ->
                         [%expr ([%e vars_expr] @ acc, [%e abt_expr])]
                       | `Expr expr ->
                         [%expr
                           let (vars, [%p Pat.var (ident name')]) = [%e expr] in
                           (vars @ acc, [%e eident name'])
                         ])))))
           @
           [ (Nolabel, renaming)
           ; (Nolabel, Exp.construct (lident "[]") None)
           ; (Nolabel, eident name')
           ])))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     `Expr
       (Exp.apply
          (eident
             (match refer_to_simple_and_open_abts_via_module with
              | true -> String.capitalize name ^ ".apply_renaming"
              | false -> name ^ "_apply_renaming"))
          (List.map args ~f:(fun arg ->
             let (pat, expr) =
               out_code_for_open_abt
                 ~refer_to_simple_and_open_abts_via_module
                 (Uniquifier.create ())
                 (eident "renaming")
                 arg
             in
             (Nolabel,
              Exp.fun_ Nolabel None
                (Pat.var (ident "renaming"))
                (Exp.fun_ Nolabel None
                   (Pat.var (ident "acc"))
                   (Exp.fun_ Nolabel None pat
                      (match expr with
                       | `Pair (vars_expr, abt_expr) ->
                         [%expr ([%e vars_expr] @ acc, [%e abt_expr])]
                       | `Expr expr ->
                         [%expr
                           let (vars, [%p Pat.var (ident name')]) = [%e expr] in
                           (vars @ acc, [%e eident name'])
                         ])))))
           @
           [ (Nolabel, renaming)
           ; (Nolabel, Exp.construct (lident "[]") None)
           ; (Nolabel, eident name')
           ])))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     `Pair ([%expr []], [%expr With_renaming.apply_renaming [%e renaming] [%e eident name']]))
  | Open_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     `Expr
       [%expr
         [%e
           match refer_to_simple_and_open_abts_via_module with
           | true -> eident (String.capitalize name ^ ".out")
           | false -> eident (name ^ "_out")
         ]
           (With_renaming.apply_renaming
              [%e renaming]
              [%e eident name'])
       ])
  | Symbol_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name,
     `Pair
       ([%expr []],
        [%expr
          match Renaming.apply [%e renaming] [%e eident name] with
          | Internal_var.Free_var var -> var
          | Internal_var.Bound_var _ -> failwith "Internal Abbot error."]))
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name,
     `Pair ([%expr []], [%expr Internal_sort.apply_renaming [%e renaming] [%e eident name]]))
  | Prod abts ->
    let (pats, exprs) =
      List.map abts ~f:(out_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier renaming)
      |> List.unzip
    in
    (* CR wduff: The names in here need to be uniquified. *)
    let (lets, vars_exprs, abt_exprs) =
      List.mapi exprs ~f:(fun i expr ->
        match expr with
        | `Pair (vars_expr, abt_expr) ->
          (None, vars_expr, abt_expr)
        | `Expr expr ->
          let vars_var = sprintf "vars_%d" i in
          (* CR wduff: Is "external" the right name? Why? *)
          let abt_var = sprintf "external_%d" i in
          let let_pat = [%pat? ([%p pvar vars_var], [%p pvar abt_var])] in
          let let_expr = expr in
          (Some (let_pat, let_expr), eident vars_var, eident abt_var))
      |> unzip3
    in
    let lets = List.filter_opt lets in
    let vars_expr =
      List.fold_right vars_exprs
        ~init:[%expr []]
        ~f:(fun vars_expr acc ->
          [%expr [%e vars_expr] @ [%e acc] ])
    in
    let abt_expr = Exp.tuple abt_exprs in
    (Pat.tuple pats,
     (match lets with
      | [] ->
        `Pair (vars_expr, abt_expr)
      | _::_ ->
        `Expr
          (List.fold_right lets
             ~init:[%expr ([%e vars_expr], [%e abt_expr])]
             ~f:(fun (let_pat, let_expr) acc ->
               [%expr let [%p let_pat] = [%e let_expr] in [%e acc]]))))
  | Symbol_binding name ->
    let bound_name = Uniquifier.uniquify uniquifier ("bound_" ^ name ^ "_name") in
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar bound_name,
     `Expr
       [%expr
         let [%p pvar name'] = Temp.create [%e eident bound_name] in
         ([[%e eident name']], [%e eident name'])
       ])
  | Sort_binding sort ->
    let bound_name = Uniquifier.uniquify uniquifier ("bound_" ^ sort ^ "_name") in
    let var_name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
    (pvar bound_name,
     `Expr
       [%expr
         let [%p pvar var_name] = Temp.create [%e eident bound_name] in
         ([[%e eident var_name]], [%e eident var_name])
       ])
;;

let rec out_code_for_closed_abt
          ~refer_to_simple_and_open_abts_via_module
          uniquifier
          renaming
          (abt : [ `Closed ] Abt.t) =
  match abt with
  | Builtin_abt_use (builtin_abt, args) ->
    (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
    let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   out_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     (eident "renaming")
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, renaming)
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Simple_abt_use (name, args) ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     Exp.let_ Nonrecursive
       [ Vb.mk
           (Pat.tuple [ Pat.any (); Pat.var (ident name') ])
           (Exp.apply
              (eident
                 (match refer_to_simple_and_open_abts_via_module with
                  | true -> String.capitalize name ^ ".apply_renaming"
                  | false -> name ^ "_apply_renaming"))
              (List.map args ~f:(fun arg ->
                 let (pat, expr) =
                   out_code_for_closed_abt
                     ~refer_to_simple_and_open_abts_via_module
                     (Uniquifier.create ())
                     (eident "renaming")
                     arg
                 in
                 (Nolabel,
                  Exp.fun_ Nolabel None
                    (Pat.var (ident "renaming"))
                    (Exp.fun_ Nolabel None
                       (Pat.tuple [])
                       (Exp.fun_ Nolabel None pat (Exp.tuple [ Exp.tuple []; expr ])))))
               @
               [ (Nolabel, renaming)
               ; (Nolabel, Exp.tuple [])
               ; (Nolabel, eident name')
               ]))
       ]
       (eident name'))
  | Closed_abt_use name ->
    let name' = Uniquifier.uniquify uniquifier name in
    (pvar name',
     [%expr
       With_renaming.apply_renaming
         [%e renaming]
         [%e eident name']
     ])
  | Symbol_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name,
     [%expr
       match Renaming.apply [%e renaming] [%e eident name] with
       | Internal_var.Free_var var -> var
       | Internal_var.Bound_var _ -> failwith "Internal Abbot error."
     ])
  | Sort_use name ->
    let name = Uniquifier.uniquify uniquifier name in
    (pvar name, [%expr Internal_sort.apply_renaming [%e renaming] [%e eident name]])
  | Prod abts ->
    let (pats, exprs) =
      List.map abts
        ~f:(out_code_for_closed_abt
              ~refer_to_simple_and_open_abts_via_module
              uniquifier
              renaming)
      |> List.unzip
    in
    (Pat.tuple pats, Exp.tuple exprs)
  | Bind (lhs, rhs) ->
    let (lhs_pat, lhs_expr) =
      out_code_for_open_abt ~refer_to_simple_and_open_abts_via_module uniquifier renaming lhs
    in
    let (rhs_pat, rhs_expr) =
      apply_renaming_code_for_closed_abt
        ~refer_to_simple_and_open_abts_via_module
        uniquifier
        [%expr renaming]
        rhs
    in
    ([%pat? ([%p lhs_pat], [%p rhs_pat])],
     (match lhs_expr with
      | `Pair (lhs_vars_expr, lhs_abt_expr) ->
        [%expr
          let renaming = Renaming.unbind' [%e renaming] [%e lhs_vars_expr] in
          ([%e lhs_abt_expr], [%e rhs_expr])
        ]
      | `Expr lhs_expr ->
        [%expr
          let (vars, lhs) = [%e lhs_expr] in
          let renaming = Renaming.unbind' [%e renaming] vars in
          (lhs, [%e rhs_expr])
        ]))
;;

let apply_renaming_code_for_simple_cases ~refer_to_simple_and_open_abts_via_module cases =
  List.map cases ~f:(fun (constructor_name, abt_opt) ->
    match abt_opt with
    | None ->
      { pc_lhs = Pat.construct (lident constructor_name) None
      ; pc_guard = None
      ; pc_rhs =
          Exp.tuple
            [ eident "acc"
            ; Exp.construct (lident constructor_name) None
            ]
      }
    | Some abt ->
      let (pat, expr) =
        apply_renaming_code_for_simple_abt
          ~refer_to_simple_and_open_abts_via_module
          (Uniquifier.create ())
          (eident "renaming")
          (eident "acc")
          abt
      in
      { pc_lhs = Pat.construct (lident constructor_name) (Some pat)
      ; pc_guard = None
      ; pc_rhs =
          [%expr
            let (acc, args) = [%e expr] in
            (acc,
             [%e
               Exp.construct
                 (lident constructor_name)
                 (Some (eident "args"))
             ])
          ]
      })
;;

let into_code_for_open_cases
      ~make_internal_constructor_name
      ~refer_to_simple_and_open_abts_via_module
      cases
  =
  List.map cases ~f:(fun (constructor_name, abt_opt) ->
    match abt_opt with
    | None ->
      { pc_lhs = Pat.construct (lident constructor_name) None
      ; pc_guard = None
      ; pc_rhs =
          [%expr
            ([],
             [%e
               Exp.construct
                 (lident (make_internal_constructor_name ~constructor_name))
                 None
             ])
          ]
      }
    | Some abt ->
      let (pat, expr) =
        into_code_for_open_abt
          ~refer_to_simple_and_open_abts_via_module
          (Uniquifier.create ())
          abt
      in
      { pc_lhs = Pat.construct (lident constructor_name) (Some pat)
      ; pc_guard = None
      ; pc_rhs =
          (match expr with
           | `Pair (vars_expr, abt_expr) ->
             [%expr
               ([%e vars_expr],
                [%e
                  Exp.construct
                    (lident (make_internal_constructor_name ~constructor_name))
                    (Some abt_expr)
                ])
             ]
           | `Expr expr ->
             [%expr
               let (vars, args) = [%e expr] in
               (vars,
                [%e
                  Exp.construct
                    (lident (make_internal_constructor_name ~constructor_name))
                    (Some (eident "args"))
                ])
             ])
      })
;;

let into_code_for_closed_cases
      ~make_internal_constructor_name
      ~refer_to_simple_and_open_abts_via_module
      cases
  =
  List.map cases ~f:(fun (constructor_name, abt) ->
    match abt with
    | None ->
      { pc_lhs = Pat.construct (lident constructor_name) None
      ; pc_guard = None
      ; pc_rhs =
          Exp.construct
            (lident (make_internal_constructor_name ~constructor_name))
            None
      }
    | Some abt ->
      let (pat, expr) =
        into_code_for_closed_abt
          ~refer_to_simple_and_open_abts_via_module
          (Uniquifier.create ())
          abt
      in
      { pc_lhs = Pat.construct (lident constructor_name) (Some pat)
      ; pc_guard = None
      ; pc_rhs =
          Exp.construct
            (lident (make_internal_constructor_name ~constructor_name))
            (Some expr)
      })
;;

let out_code_for_open_cases
      ~make_internal_constructor_name
      ~refer_to_simple_and_open_abts_via_module
      cases
  =
  List.map cases ~f:(fun (constructor_name, abt) ->
    match abt with
    | None ->
      { pc_lhs =
          Pat.construct
            (lident (make_internal_constructor_name ~constructor_name))
            None
      ; pc_guard = None
      ; pc_rhs = [%expr ([], [%e Exp.construct (lident constructor_name) None])]
      }
    | Some abt ->
      let (pat, expr) =
        out_code_for_open_abt
          ~refer_to_simple_and_open_abts_via_module
          (Uniquifier.create ())
          [%expr renaming]
          abt
      in
      { pc_lhs =
          Pat.construct
            (lident (make_internal_constructor_name ~constructor_name))
            (Some pat)
      ; pc_guard = None
      ; pc_rhs =
          (match expr with
           | `Pair (vars_expr, abt_expr) ->
             [%expr
               ([%e vars_expr],
                [%e
                  Exp.construct
                    (lident constructor_name)
                    (Some abt_expr)
                ])
             ]
           | `Expr expr ->
             [%expr
               let (vars, args) = [%e expr] in
               (vars,
                [%e
                  Exp.construct
                    (lident constructor_name)
                    (Some (eident "args"))
                ])
             ])
      })
;;

let out_code_for_closed_cases
      ~make_internal_constructor_name
      ~refer_to_simple_and_open_abts_via_module
      cases
  =
  List.map cases ~f:(fun (constructor_name, abt) ->
    match abt with
    | None ->
      { pc_lhs = Pat.construct (lident (make_internal_constructor_name ~constructor_name)) None
      ; pc_guard = None
      ; pc_rhs = Exp.construct (lident constructor_name) None
      }
    | Some abt ->
      let (pat, expr) =
        out_code_for_closed_abt
          ~refer_to_simple_and_open_abts_via_module
          (Uniquifier.create ())
          (* CR wduff: This should be an argument. *)
          [%expr renaming]
          abt
      in
      { pc_lhs =
          Pat.construct (lident (make_internal_constructor_name ~constructor_name)) (Some pat)
      ; pc_guard = None
      ; pc_rhs = Exp.construct (lident constructor_name) (Some expr)
      })
;;

let rec subst_code_for_abt
  : type a.
    refer_to_others_via_module:bool
  -> (arg_label * string) list
  -> Uniquifier.t
  -> a Abt.t
  -> pattern * expression
  =
  fun ~refer_to_others_via_module sub uniquifier abt ->
    match abt with
    | Arg_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident ("subst_" ^ name))
         (List.map sub ~f:(fun (arg_label, arg_name) ->
            (arg_label, eident arg_name))
          @
          [ (Nolabel, (eident name')) ]))
    | Builtin_abt_use (builtin_abt, args) ->
      (* CR wduff: This duplicates a lot of code with [Simple_abt_use]. *)
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (Pat.var (ident name'),
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".subst"))
         (List.map args ~f:(fun arg ->
            let (pat, expr) =
              subst_code_for_abt
                ~refer_to_others_via_module
                sub
                (Uniquifier.create ())
                arg
            in
            (Nolabel,
             List.fold_right sub ~init:(Exp.fun_ Nolabel None pat expr)
               ~f:(fun (arg_label, arg_name) expr ->
                 Exp.fun_ arg_label None (pvar arg_name) expr)))
          @
          List.map sub ~f:(fun (arg_label, arg_name) ->
            (arg_label, eident arg_name))
          @
          [ (Nolabel, eident name') ]))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (Pat.var (ident name'),
       Exp.apply
         (eident
            (match refer_to_others_via_module with
             | true -> String.capitalize name ^ ".subst"
             | false -> name ^ "_subst"))
         (List.map args ~f:(fun arg ->
            let (pat, expr) =
              subst_code_for_abt
                ~refer_to_others_via_module
                sub
                (Uniquifier.create ())
                arg
            in
            (Nolabel,
             List.fold_right sub ~init:(Exp.fun_ Nolabel None pat expr)
               ~f:(fun (arg_label, arg_name) expr ->
                 Exp.fun_ arg_label None (pvar arg_name) expr)))
          @
          List.map sub ~f:(fun (arg_label, arg_name) ->
            (arg_label, eident arg_name))
          @
          [ (Nolabel, eident name') ]))
    | Open_abt_use name ->
      (* CR wduff: It's sad that this case is duplicated. *)
      let name' = Uniquifier.uniquify uniquifier name in
      (Pat.var (ident name'),
       Exp.apply
         (eident
            (match refer_to_others_via_module with
             | true -> String.capitalize name ^ ".subst"
             | false -> name ^ "_subst"))
         (List.map sub ~f:(fun (arg_label, arg_name) ->
            (arg_label, eident arg_name))
          @
          [ (Nolabel, eident name') ]))
    | Closed_abt_use name | Sort_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (Pat.var (ident name'),
       Exp.apply
         (eident
            (match refer_to_others_via_module with
             | true -> String.capitalize name ^ ".subst"
             | false -> name ^ "_subst"))
         (List.map sub ~f:(fun (arg_label, arg_name) ->
            (arg_label, eident arg_name))
            @
            [ (Nolabel, eident name') ]))
    | Symbol_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (Pat.var (ident name'), eident name')
    | Prod abts ->
      let (pats, exps) =
        List.map abts ~f:(subst_code_for_abt ~refer_to_others_via_module sub uniquifier)
        |> List.unzip
      in
      (Pat.tuple pats, Exp.tuple exps)
    | Symbol_binding name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (Pat.var (ident name'), eident name')
    | Sort_binding sort ->
      let name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
      (pvar name, eident name)
    | Bind (lhs, rhs) ->
      let (lhs_pat, lhs_expr) = subst_code_for_abt ~refer_to_others_via_module sub uniquifier lhs in
      let (rhs_pat, rhs_expr) = subst_code_for_abt ~refer_to_others_via_module sub uniquifier rhs in
      (Pat.tuple [ lhs_pat; rhs_pat ], Exp.tuple [ lhs_expr; rhs_expr ])
;;

let subst_code_for_cases ~make_exposed_constructor_name ~refer_to_others_via_module sub cases =
  List.map cases ~f:(fun (constructor_name, abt) ->
    let constructor_name = make_exposed_constructor_name ~constructor_name in
    match abt with
    | None ->
      { pc_lhs = Pat.construct (lident constructor_name) None
      ; pc_guard = None
      ; pc_rhs =
          Exp.construct (lident constructor_name) None
      }
    | Some abt ->
      let (pat, expr) =
        subst_code_for_abt ~refer_to_others_via_module sub (Uniquifier.create ()) abt
      in
      { pc_lhs =
          Pat.construct (lident constructor_name) (Some pat)
      ; pc_guard = None
      ; pc_rhs =
          Exp.construct (lident constructor_name) (Some expr)
      })
;;
