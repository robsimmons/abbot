open! Core
open Ppxlib
open Ast_helper
open Typed

let rec unzip3 = function
  | [] -> ([], [], [])
  | (x, y, z) :: rest ->
    let (xs, ys, zs) = unzip3 rest in
    (x :: xs, y :: ys, z :: zs)

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
  : type a. refer_to_via_module:(string -> bool) -> lang:[ `Ocaml | `Sml ] -> a Abt.t -> core_type =
  fun ~refer_to_via_module ~lang abt ->
  match abt with
  | Arg_use name ->
    Typ.var name
  | Builtin_abt_use (builtin_abt, args) ->
    Typ.constr
      (lident (Builtin_abt.module_name builtin_abt ^ ".t"))
      (List.map args ~f:(internal_type_of_abt ~refer_to_via_module ~lang))
  | Simple_abt_use (name, args) ->
    type_t
      ~via_module:(refer_to_via_module name)
      ~args:(List.map args ~f:(internal_type_of_abt ~refer_to_via_module ~lang))
      name
  | Closed_abt_use name | Sort_use name ->
    type_t ~via_module:(refer_to_via_module name) name
  | Symbol_use (_ : string) ->
    Typ.constr (lident "Internal_var.t") []
  | Open_abt_use name ->
    type_internal ~via_module:(refer_to_via_module name) name
  | Prod abts ->
    Typ.tuple (List.map abts ~f:(internal_type_of_abt ~refer_to_via_module ~lang))
  | Symbol_binding _ | Sort_binding _ ->
    begin
      match lang with
      | `Ocaml -> [%type: string compare_ignore]
      | `Sml -> [%type: string]
    end
  | Bind (lhs, rhs) ->
    Typ.constr (lident "bind")
      [ internal_type_of_abt ~refer_to_via_module ~lang lhs
      ; internal_type_of_abt ~refer_to_via_module ~lang rhs
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
      let pat = pvar convenient_constructor_name in
      match abt_opt with
      | None ->
        Str.value Nonrecursive
          [ Vb.mk
              pat
              (Exp.fun_ Nolabel None
                 [%pat? ()]
                 (Exp.apply
                    (eident "into")
                    [ (Nolabel, eident constructor_name) ]))
          ]
      | Some _ ->
        Str.value Nonrecursive
          [ Vb.mk
              pat
              (Exp.fun_ Nolabel None
                 (pvar "arg")
                 (Exp.apply
                    (eident "into")
                    [ (Nolabel,
                       Exp.apply
                         (eident constructor_name)
                         [ (Nolabel, eident "arg") ])
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

  let uniquify t name =
    let name =
      (* If [name] ends in a number, drop it and choose a new one, to avoid names that already end
         in numbers colliding with names that have the same non-number prefix and get a number from
         [uniquify]. *)
      String.rstrip name ~drop:(fun char -> Char.is_digit char)
    in
    let int = Hashtbl.find_or_add t name ~default:(fun () -> 1) in
    Hashtbl.set t ~key:name ~data:(int + 1);
    sprintf "%s%d" name int
end

let internal_error_message = [%expr "Internal Abbot error occurred. Please report this bug."]

(* CR wduff: Can some of these functions be merged now that we have a GADT? Does that actually make
   the code better?

   We end up with slightly more code, and a gross assert false. We can probably just better factor
   the existing code and reduce its size considerably. The basic issue is that by cutting down to a
   single match, you only save work in the boring cases, because you have to do a bunch of combining
   work in the other cases.

   Another idea would be to save code across into/out instead of accross open/closed. You could
   maybe write a [fold_map]-like function for open abts and use it for both into and out.
*)

(* CR wduff: We could produce nicer code if we keep [vars] as a compile time list when possible,
   allowing compile-time concatenation. *)

module Walks (Config : sig
    val use_flat_names_internally : bool
    val qualify_constructors : bool
    val raise_internal_error_expr : Ppxlib.expression
  end)
=
struct
  let rec apply_renaming_code_for_simple_abt
            uniquifier
            ~renaming
            ~acc
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
         ; (Nolabel, eident name')
         ],
       `Used_renaming)
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
         (apply_renaming_code_for_simple_abt_args args
          @
          [ (Nolabel, renaming)
          ; (Nolabel, acc)
          ; (Nolabel, eident name')
          ]),
       `Used_renaming)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_renaming"
             | false -> String.capitalize name ^ ".apply_renaming"))
         (apply_renaming_code_for_simple_abt_args args
          @
          [ (Nolabel, renaming)
          ; (Nolabel, acc)
          ; (Nolabel, eident name')
          ]),
       `Used_renaming)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         ([%e acc],
          With_renaming.apply_renaming
            [%e renaming]
            [%e eident name'])
       ],
       `Used_renaming)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr Renaming.apply [%e renaming] [%e eident name]], `Used_renaming)
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       [%expr ([%e acc], Internal_sort.apply_renaming renaming [%e eident name])],
       `Used_renaming)
    | Prod abts ->
      let rec make_tuple_fold i acc abts =
        match abts with
        | [] ->
          ([],
           Exp.tuple
             [ eident "acc"
             ; Exp.tuple (List.init i ~f:(fun i -> eident (sprintf "result_%d" i)))
             ],
           `Ignored_renaming)
        | abt :: abts ->
          let (pat, expr, used_renaming) =
            apply_renaming_code_for_simple_abt
              uniquifier
              ~renaming
              ~acc
              abt
          in
          let (pats, expr', used_renaming') = make_tuple_fold (i + 1) (eident "acc") abts in
          (pat :: pats,
           [%expr let (acc, [%p pvar (sprintf "result_%d" i)]) = [%e expr] in [%e expr']],
           match used_renaming, used_renaming' with
           | `Used_renaming, _ | _, `Used_renaming -> `Used_renaming
           | `Ignored_renaming, `Ignored_renaming -> `Ignored_renaming)
      in
      let (pats, expr, used_renaming) = make_tuple_fold 0 acc abts in
      (Pat.tuple pats, expr, used_renaming)

  and apply_renaming_code_for_simple_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr, used_renaming) =
        apply_renaming_code_for_simple_abt
          (Uniquifier.create ())
          ~renaming:(eident "renaming")
          ~acc:(eident "acc")
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (match used_renaming with
          | `Used_renaming -> pvar "renaming"
          | `Ignored_renaming -> pvar "_renaming")
         (Exp.fun_ Nolabel None
            (pvar "acc")
            (Exp.fun_ Nolabel None pat expr))))
  ;;

  let used_renaming_of_list used_renaming_list =
    (match
       List.exists used_renaming_list ~f:(function
         | `Used_renaming -> true
         | `Ignored_renaming -> false)
     with
     | true -> `Used_renaming
     | false -> `Ignored_renaming)
  ;;

  (* CR wduff: This is duplicated from the ocaml code. *)
  let string_of_arg ~arg_count =
    match arg_count with
    | 0 -> (fun _ _ -> assert false)
    | 1 -> (fun prefix _ -> prefix)
    | _ -> (fun prefix i -> prefix ^ Int.to_string (i + 1))
  ;;

  let rec apply_renaming_code_for_closed_abt
            uniquifier
            ~renaming
            (abt : [ `Closed ] Abt.t)
    =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      let (arg_funs, used_renaming) = apply_renaming_code_for_closed_abt_args renaming args in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".map"))
         ((Nolabel, eident name') :: arg_funs),
       used_renaming)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      let (arg_funs, used_renaming) = apply_renaming_code_for_closed_abt_args renaming args in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_map"
             | false -> String.capitalize name ^ ".map"))
         ((Nolabel, eident name') :: arg_funs),
       used_renaming)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr With_renaming.apply_renaming [%e renaming] [%e eident name']],
       `Used_renaming)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr Renaming.apply [%e renaming] [%e eident name]], `Used_renaming)
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr Internal_sort.apply_renaming [%e renaming] [%e eident name]], `Used_renaming)
    | Prod abts ->
      let (pats, exprs, used_renaming) =
        List.map abts ~f:(apply_renaming_code_for_closed_abt uniquifier ~renaming)
        |> List.unzip3
      in
      (Pat.tuple pats, Exp.tuple exprs, used_renaming_of_list used_renaming)
    | Bind (_, _) ->
      (* CR wduff: Implement?

         I suspect what has to happen here is we need to shift before we apply it to the rhs, since
         it will have moved underneath a binding site.

         A nasty way to do this that would mimic what we do when there is an indirection is unbind,
         apply the renaming, and then rebind. (this is basically a conjugate operation).

         Maybe it suffices to prove that the shift is equivalent to the conjugation.

         It's not the same as shift, because you need to ignore vars bound by this thing, and
         subtract from the other bound vars. This is clear from the implementation of [unbind]. *)
      failwith "unimpl"

  and apply_renaming_code_for_closed_abt_args renaming args =
    let string_of_arg = string_of_arg ~arg_count:(List.length args) in
    let (args, used_renaming) =
      List.mapi args ~f:(fun arg_num arg ->
        let (pat, expr, used_renaming) =
          apply_renaming_code_for_closed_abt
            (Uniquifier.create ())
            ~renaming
            arg
        in
        (* CR wduff: We need to not label arguments in sml... *)
        ((Labelled (string_of_arg "f" arg_num),
          Exp.fun_ Nolabel None pat expr),
         used_renaming))
      |> List.unzip
    in
    (args, used_renaming_of_list used_renaming)
  ;;

  let vars_to_expr = function
    | `Expr expr -> expr
    | `List vars ->
      List.fold_right vars ~init:[%expr []] ~f:(fun var vars -> [%expr [%e var] :: [%e vars]])

  let append_vars vars1 vars2 =
    match (vars1, vars2) with
    | (`List vars1, `List vars2) ->
      `List (vars1 @ vars2)
    | (`Expr expr, `List []) | (`List [], `Expr expr) ->
      `Expr expr
    | (`Expr _, _) | (_, `Expr _) ->
      `Expr [%expr [%e vars_to_expr vars1] @ [%e vars_to_expr vars2]]

  let rec into_code_for_open_abt uniquifier (abt : [ `Open ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       `Expr
         (Exp.apply
            (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
            (into_code_for_open_abt_args args
             @
             [ (Nolabel, eident "Renaming.ident")
             ; (Nolabel, [%expr []])
             ; (Nolabel, eident name')
             ])))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Expr
         (Exp.apply
            (eident
               (match Config.use_flat_names_internally with
                | true -> name ^ "_apply_renaming"
                | false -> String.capitalize name ^ ".apply_renaming"))
            (into_code_for_open_abt_args args
             @
             [ (Nolabel, eident "Renaming.ident")
             ; (Nolabel, [%expr []])
             ; (Nolabel, eident name')
             ])))
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name', `Pair (`List [], eident name'))
    | Open_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Expr
         [%expr
           [%e
             match Config.use_flat_names_internally with
             | true -> eident (name ^ "_into")
             | false -> eident (String.capitalize name ^ ".into")]
             [%e eident name']])
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, `Pair (`List [], [%expr Internal_var.Free_var [%e eident name]]))
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, `Pair (`List [], eident name))
    | Prod abts ->
      let (pats, exprs) =
        List.map abts ~f:(into_code_for_open_abt uniquifier)
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
            let abt_var = sprintf "inner_%d" i in
            let let_pat = [%pat? ([%p pvar vars_var], [%p pvar abt_var])] in
            let let_expr = expr in
            (Some (let_pat, let_expr), `Expr (eident vars_var), eident abt_var))
        |> unzip3
      in
      let lets = List.filter_opt lets in
      let vars_expr =
        List.fold_right vars_exprs
          ~init:(`List [])
          ~f:(fun vars_expr acc ->
            append_vars vars_expr acc)
      in
      let abt_expr = Exp.tuple abt_exprs in
      (Pat.tuple pats,
       (match lets with
        | [] ->
          `Pair (vars_expr, abt_expr)
        | _::_ ->
          `Expr
            (List.fold_right lets
               ~init:[%expr ([%e vars_to_expr vars_expr], [%e abt_expr])]
               ~f:(fun (let_pat, let_expr) acc ->
                 [%expr let [%p let_pat] = [%e let_expr] in [%e acc]]))))
    | Symbol_binding name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name', `Pair (`List [eident name'], [%expr Temp.name [%e eident name']]))
    | Sort_binding sort ->
      let name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
      (pvar name, `Pair (`List [eident name], [%expr Temp.name [%e eident name]]))

  and into_code_for_open_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) =
        into_code_for_open_abt
          (Uniquifier.create ())
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         [%pat? _]
         (Exp.fun_ Nolabel None
            (pvar "acc")
            (Exp.fun_ Nolabel None pat
               (match expr with
                | `Pair (vars_expr, abt_expr) ->
                  [%expr ([%e vars_to_expr vars_expr] @ acc, [%e abt_expr])]
                | `Expr expr ->
                  [%expr
                    let (vars, inner) = [%e expr] in
                    (vars @ acc, inner)
                  ])))))
  ;;

  let rec into_code_for_closed_abt uniquifier (abt : [ `Closed ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       [%expr
         let ((), [%p pvar name']) =
           [%e
             Exp.apply
               (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
               (into_code_for_closed_abt_args args
                @
                [ (Nolabel, eident "Renaming.ident")
                ; (Nolabel, [%expr ()])
                ; (Nolabel, eident name')
                ])
           ]
         in
         [%e eident name']
       ])
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         let ((), [%p pvar name']) =
           [%e
             Exp.apply
               (eident
                  (match Config.use_flat_names_internally with
                   | true -> name ^ "_apply_renaming"
                   | false -> String.capitalize name ^ ".apply_renaming"))
               (into_code_for_closed_abt_args args
                @
                [ (Nolabel, eident "Renaming.ident")
                ; (Nolabel, [%expr ()])
                ; (Nolabel, eident name')
                ])
           ]
         in
         [%e eident name']
       ])
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name', eident name')
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr Internal_var.Free_var [%e eident name]])
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, eident name)
    | Prod abts ->
      let (pats, exprs) =
        List.map abts ~f:(into_code_for_closed_abt uniquifier)
        |> List.unzip
      in
      (Pat.tuple pats, Exp.tuple exprs)
    | Bind (lhs, rhs) ->
      let (lhs_pat, lhs_expr) =
        into_code_for_open_abt uniquifier lhs
      in
      let (rhs_pat, rhs_expr, used_renaming) =
        apply_renaming_code_for_closed_abt
          uniquifier
          ~renaming:[%expr renaming]
          rhs
      in
      let renaming_pat =
        (* CR wduff: If the renaming is unused, we don't need to compute it. *)
        match used_renaming with
        | `Used_renaming -> pvar "renaming"
        | `Ignored_renaming -> pvar "_renaming"
      in
      ([%pat? ([%p lhs_pat], [%p rhs_pat])],
       (match lhs_expr with
        | `Pair (lhs_vars_expr, lhs_abt_expr) ->
          [%expr
            let [%p renaming_pat] = Renaming.bind' [%e vars_to_expr lhs_vars_expr] in
            ([%e lhs_abt_expr], [%e rhs_expr])
          ]
        | `Expr lhs_expr ->
          [%expr
            let (vars, lhs) = [%e lhs_expr] in
            let [%p renaming_pat] = Renaming.bind' vars in
            (lhs, [%e rhs_expr])
          ]))

  and into_code_for_closed_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) =
        into_code_for_closed_abt
          (Uniquifier.create ())
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         [%pat? _]
         (Exp.fun_ Nolabel None
            [%pat? ()]
            (Exp.fun_ Nolabel None pat [%expr ((), [%e expr])]))))
  ;;

  let rec out_code_for_open_abt uniquifier renaming (abt : [ `Open ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       `Expr
         (Exp.apply
            (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
            (out_code_for_open_abt_args args
             @
             [ (Nolabel, renaming)
             ; (Nolabel, [%expr []])
             ; (Nolabel, eident name')
             ])))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Expr
         (Exp.apply
            (eident
               (match Config.use_flat_names_internally with
                | true -> name ^ "_apply_renaming"
                | false -> String.capitalize name ^ ".apply_renaming"))
            (out_code_for_open_abt_args args
             @
             [ (Nolabel, renaming)
             ; (Nolabel, [%expr []])
             ; (Nolabel, eident name')
             ])))
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Pair (`List [], [%expr With_renaming.apply_renaming [%e renaming] [%e eident name']]))
    | Open_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Expr
         [%expr
           [%e
             match Config.use_flat_names_internally with
             | true -> eident (name ^ "_out")
             | false -> eident (String.capitalize name ^ ".out")
           ]
             (With_renaming.apply_renaming
                [%e renaming]
                [%e eident name'])
         ])
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       `Pair
         (`List [],
          [%expr
            match Renaming.apply [%e renaming] [%e eident name] with
            | Internal_var.Free_var var -> var
            | Internal_var.Bound_var _ -> [%e Config.raise_internal_error_expr]]))
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       `Pair (`List [], [%expr Internal_sort.apply_renaming [%e renaming] [%e eident name]]))
    | Prod abts ->
      let (pats, exprs) =
        List.map abts ~f:(out_code_for_open_abt uniquifier renaming)
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
            let abt_var = sprintf "outer_%d" i in
            let let_pat = [%pat? ([%p pvar vars_var], [%p pvar abt_var])] in
            let let_expr = expr in
            (Some (let_pat, let_expr), `Expr (eident vars_var), eident abt_var))
        |> unzip3
      in
      let lets = List.filter_opt lets in
      let vars_expr =
        List.fold_right vars_exprs
          ~init:(`List [])
          ~f:(fun vars_expr acc ->
            append_vars vars_expr acc)
      in
      let abt_expr = Exp.tuple abt_exprs in
      (Pat.tuple pats,
       (match lets with
        | [] ->
          `Pair (vars_expr, abt_expr)
        | _::_ ->
          `Expr
            (List.fold_right lets
               ~init:[%expr ([%e vars_to_expr vars_expr], [%e abt_expr])]
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

  and out_code_for_open_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) =
        out_code_for_open_abt
          (Uniquifier.create ())
          (eident "renaming")
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (pvar "renaming")
         (Exp.fun_ Nolabel None
            (pvar "acc")
            (Exp.fun_ Nolabel None pat
               (match expr with
                | `Pair (vars_expr, abt_expr) ->
                  [%expr ([%e vars_to_expr vars_expr] @ acc, [%e abt_expr])]
                | `Expr expr ->
                  [%expr
                    let (vars, outer) = [%e expr] in
                    (vars @ acc, outer)
                  ])))))
  ;;

  let rec out_code_for_closed_abt
            uniquifier
            renaming
            (abt : [ `Closed ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       [%expr
         let ((), [%p pvar name']) =
           [%e
             Exp.apply
               (eident (Builtin_abt.module_name builtin_abt ^ ".apply_renaming"))
               (out_code_for_closed_abt_args args
                @
                [ (Nolabel, renaming)
                ; (Nolabel, [%expr ()])
                ; (Nolabel, eident name')
                ])
           ]
         in
         [%e eident name']
       ])
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         let ((), [%p pvar name']) =
           [%e
             Exp.apply
               (eident
                  (match Config.use_flat_names_internally with
                   | true -> name ^ "_apply_renaming"
                   | false -> String.capitalize name ^ ".apply_renaming"))
               (out_code_for_closed_abt_args args
                @
                [ (Nolabel, renaming)
                ; (Nolabel, [%expr ()])
                ; (Nolabel, eident name')
                ])
           ]
         in
         [%e eident name']
       ])
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
         | Internal_var.Bound_var _ -> [%e Config.raise_internal_error_expr]
       ])
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr Internal_sort.apply_renaming [%e renaming] [%e eident name]])
    | Prod abts ->
      let (pats, exprs) =
        List.map abts
          ~f:(out_code_for_closed_abt
                uniquifier
                renaming)
        |> List.unzip
      in
      (Pat.tuple pats, Exp.tuple exprs)
    | Bind (lhs, rhs) ->
      let (lhs_pat, lhs_expr) =
        out_code_for_open_abt uniquifier renaming lhs
      in
      let (rhs_pat, rhs_expr, used_renaming) =
        apply_renaming_code_for_closed_abt
          uniquifier
          ~renaming:[%expr renaming]
          rhs
      in
      let renaming_pat =
        (* CR wduff: If the renaming is unused, we don't need to compute it. *)
        match used_renaming with
        | `Used_renaming -> pvar "renaming"
        | `Ignored_renaming -> pvar "_renaming"
      in
      ([%pat? ([%p lhs_pat], [%p rhs_pat])],
       (match lhs_expr with
        | `Pair (lhs_vars_expr, lhs_abt_expr) ->
          [%expr
            let [%p renaming_pat] =
              Renaming.unbind' [%e renaming] [%e vars_to_expr lhs_vars_expr]
            in
            ([%e lhs_abt_expr], [%e rhs_expr])
          ]
        | `Expr lhs_expr ->
          [%expr
            let (vars, lhs) = [%e lhs_expr] in
            let [%p renaming_pat] = Renaming.unbind' [%e renaming] vars in
            (lhs, [%e rhs_expr])
          ]))

  and out_code_for_closed_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) =
        out_code_for_closed_abt
          (Uniquifier.create ())
          (eident "renaming")
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (pvar "renaming")
         (Exp.fun_ Nolabel None
            [%pat? ()]
            (Exp.fun_ Nolabel None pat [%expr ((), [%e expr])]))))
  ;;

  let apply_renaming_code_for_simple_cases ~renaming ~acc cases =
    let (cases, used_renaming) =
      List.map cases ~f:(fun (constructor_name, abt_opt) ->
        let (pat, expr, used_renaming) =
          match abt_opt with
          | None ->
            (Pat.construct (lident constructor_name) None,
             Exp.tuple
               [ eident "acc"
               ; Exp.construct (lident constructor_name) None
               ],
             `Ignored_renaming)
          | Some abt ->
            let (pat, expr, used_renaming) =
              apply_renaming_code_for_simple_abt
                (Uniquifier.create ())
                ~renaming
                ~acc
                abt
            in
            (Pat.construct (lident constructor_name) (Some pat),
             [%expr
               let (acc, args) = [%e expr] in
               (acc,
                [%e
                  Exp.construct
                    (lident constructor_name)
                    (Some (eident "args"))
                ])
             ],
             used_renaming)
        in
        (Exp.case pat expr, used_renaming))
      |> List.unzip
    in
    (cases, used_renaming_of_list used_renaming)
  ;;

  let make_internal_constructor_name ~name_of_walked_value ~constructor_name =
    match Config.qualify_constructors with
    | false -> constructor_name
    | true ->
      match Config.use_flat_names_internally with
      | true -> String.capitalize name_of_walked_value ^ "_" ^ constructor_name
      | false -> String.capitalize name_of_walked_value ^ "." ^ constructor_name
  ;;

  let make_exposed_constructor_name ~name_of_walked_value ~constructor_name =
    match Config.qualify_constructors with
    | false -> constructor_name
    | true -> String.capitalize name_of_walked_value ^ "." ^ constructor_name
  ;;

  let into_code_for_open_cases ~name_of_walked_value cases =
    List.map cases ~f:(fun (constructor_name, abt_opt) ->
      let internal_constructor =
        lident (make_internal_constructor_name ~name_of_walked_value ~constructor_name)
      in
      let (pat, expr) =
        match abt_opt with
        | None ->
          (Pat.construct (lident constructor_name) None,
           [%expr ([], [%e Exp.construct internal_constructor None])])
        | Some abt ->
          let (pat, expr) =
            into_code_for_open_abt
              (Uniquifier.create ())
              abt
          in
          (Pat.construct (lident constructor_name) (Some pat),
           (match expr with
            | `Pair (vars_expr, abt_expr) ->
              [%expr
                ([%e vars_to_expr vars_expr],
                 [%e Exp.construct internal_constructor (Some abt_expr)])]
            | `Expr expr ->
              [%expr
                let (vars, args) = [%e expr] in
                (vars, [%e Exp.construct internal_constructor (Some (eident "args"))])
              ]))
      in
      Exp.case pat expr)
  ;;

  let into_code_for_closed_cases ~name_of_walked_value cases =
    List.map cases ~f:(fun (constructor_name, abt) ->
      let (pat, expr) =
        match abt with
        | None -> (None, None)
        | Some abt ->
          let (pat, expr) =
            into_code_for_closed_abt
              (Uniquifier.create ())
              abt
          in
          (Some pat, Some expr)
      in
      Exp.case
        (Pat.construct (lident constructor_name) pat)
        (Exp.construct
           (lident (make_internal_constructor_name ~name_of_walked_value ~constructor_name))
           expr))
  ;;

  let out_code_for_open_cases ~name_of_walked_value cases =
    List.map cases ~f:(fun (constructor_name, abt) ->
      let internal_constructor =
        lident (make_internal_constructor_name ~name_of_walked_value ~constructor_name)
      in
      let (pat, expr) =
        match abt with
        | None ->
          (Pat.construct internal_constructor None,
           [%expr ([], [%e Exp.construct (lident constructor_name) None])])
        | Some abt ->
          let (pat, expr) =
            out_code_for_open_abt
              (Uniquifier.create ())
              [%expr renaming]
              abt
          in
          (Pat.construct internal_constructor (Some pat),
           (match expr with
            | `Pair (vars_expr, abt_expr) ->
              [%expr
                ([%e vars_to_expr vars_expr],
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
              ]))
      in
      Exp.case pat expr)
  ;;

  let out_code_for_closed_cases ~name_of_walked_value cases =
    List.map cases ~f:(fun (constructor_name, abt) ->
      let (pat, expr) =
        match abt with
        | None ->
          (None, None)
        | Some abt ->
          let (pat, expr) =
            out_code_for_closed_abt
              (Uniquifier.create ())
              (* CR wduff: This should be an argument. *)
              [%expr renaming]
              abt
          in
          (Some pat, Some expr)
      in
      Exp.case
        (Pat.construct
           (lident (make_internal_constructor_name ~name_of_walked_value ~constructor_name))
           pat)
        (Exp.construct (lident constructor_name) expr))
  ;;

  let used_sub_of_list used_sub_list =
    (match
       List.exists used_sub_list ~f:(function
         | `Used_sub -> true
         | `Ignored_sub -> false)
     with
     | true -> `Used_sub
     | false -> `Ignored_sub)
  ;;

  let rec subst_code_for_abt
    : type a.
      sub:(arg_label * string) list
      -> Uniquifier.t
      -> a Abt.t
      -> pattern * expression * [ `Used_sub | `Ignored_sub ]
    =
    fun ~sub uniquifier abt ->
      match abt with
      | Arg_use name ->
        let name' = Uniquifier.uniquify uniquifier name in
        (pvar name',
         Exp.apply
           (eident ("subst_" ^ name))
           (List.map sub ~f:(fun (arg_label, arg_name) ->
              (arg_label, eident arg_name))
            @
            [ (Nolabel, (eident name')) ]),
         `Used_sub)
      | Builtin_abt_use (builtin_abt, args) ->
        let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
        (pvar name',
         Exp.apply
           (eident (Builtin_abt.module_name builtin_abt ^ ".subst"))
           (subst_code_for_abt_args ~sub args
            @
            List.map sub ~f:(fun (arg_label, arg_name) ->
              (arg_label, eident arg_name))
            @
            [ (Nolabel, eident name') ]),
         `Used_sub)
      | Simple_abt_use (name, args) ->
        let name' = Uniquifier.uniquify uniquifier name in
        (pvar name',
         Exp.apply
           (eident
              (match Config.use_flat_names_internally with
               | true -> name ^ "_subst"
               | false -> String.capitalize name ^ ".subst"))
           (subst_code_for_abt_args ~sub args
            @
            List.map sub ~f:(fun (arg_label, arg_name) ->
              (arg_label, eident arg_name))
            @
            [ (Nolabel, eident name') ]),
         `Used_sub)
      | Closed_abt_use name | Open_abt_use name | Sort_use name ->
        let name' = Uniquifier.uniquify uniquifier name in
        (pvar name',
         Exp.apply
           (eident
              (match Config.use_flat_names_internally with
               | true -> name ^ "_subst"
               | false -> String.capitalize name ^ ".subst"))
           (List.map sub ~f:(fun (arg_label, arg_name) ->
              (arg_label, eident arg_name))
            @
            [ (Nolabel, eident name') ]),
         `Used_sub)
      | Symbol_use name ->
        let name' = Uniquifier.uniquify uniquifier name in
        (pvar name', eident name', `Ignored_sub)
      | Prod abts ->
        let (pats, exps, used_sub) =
          List.map abts ~f:(subst_code_for_abt ~sub uniquifier)
          |> List.unzip3
        in
        (Pat.tuple pats, Exp.tuple exps, used_sub_of_list used_sub)
      | Symbol_binding name ->
        let name' = Uniquifier.uniquify uniquifier name in
        (pvar name', eident name', `Ignored_sub)
      | Sort_binding sort ->
        let name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
        (pvar name, eident name, `Ignored_sub)
      | Bind (lhs, rhs) ->
        let (lhs_pat, lhs_expr, used_sub_on_lhs) = subst_code_for_abt ~sub uniquifier lhs in
        let (rhs_pat, rhs_expr, used_sub_on_rhs) = subst_code_for_abt ~sub uniquifier rhs in
        (Pat.tuple [ lhs_pat; rhs_pat ], Exp.tuple [ lhs_expr; rhs_expr ],
         (match (used_sub_on_lhs, used_sub_on_rhs) with
          | `Used_sub, _ | _, `Used_sub -> `Used_sub
          | `Ignored_sub, `Ignored_sub -> `Ignored_sub))

  and subst_code_for_abt_args
    : type a.
      sub:(arg_label * string) list
      -> a Abt.t list
      -> (arg_label * expression) list
    =
    (fun ~sub args ->
       List.map args ~f:(fun arg ->
         let (pat, expr, used_sub) =
           subst_code_for_abt
             ~sub
             (Uniquifier.create ())
             arg
         in
         (Nolabel,
          List.fold_right sub ~init:(Exp.fun_ Nolabel None pat expr)
            ~f:(fun (arg_label, arg_name) expr ->
              Exp.fun_
                arg_label
                None
                (match used_sub with
                 | `Used_sub -> pvar arg_name
                 | `Ignored_sub -> pvar ("_" ^ arg_name))
                expr))))
  ;;

  let subst_code_for_cases ~name_of_walked_value ~sub cases =
    let (cases, used_sub) =
      List.map cases ~f:(fun (constructor_name, abt) ->
        let constructor =
          lident (make_exposed_constructor_name ~name_of_walked_value ~constructor_name)
        in
        let (pat, expr, used_sub) =
          match abt with
          | None -> (None, None, `Ignored_sub)
          | Some abt ->
            let (pat, expr, used_sub) =
              subst_code_for_abt ~sub (Uniquifier.create ()) abt
            in
            (Some pat, Some expr, used_sub)
        in
        (Exp.case (Pat.construct constructor pat) (Exp.construct constructor expr), used_sub))
      |> List.unzip
    in
    (cases, used_sub_of_list used_sub)
  ;;
end
