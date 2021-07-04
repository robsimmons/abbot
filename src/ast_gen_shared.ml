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
    Typ.constr (lident "Temp.t Internal_var.t") []
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

let use_subst = true

let apply_subst_to_var subst_expr var_expr =
  match use_subst with
  | true -> [%expr Subst.apply_to_var [%e subst_expr] [%e var_expr]]
  | false -> [%expr Renaming.apply [%e subst_expr] [%e var_expr]]
;;

let apply_subst_to_sort sort_tag subst_expr sort_expr =
  match use_subst with
  | true ->
    [%expr
      Generic_sort.apply_subst
        [%e Exp.construct (lident sort_tag) None]
        [%e subst_expr]
        [%e sort_expr]]
  | false -> [%expr Internal_sort.apply_renaming [%e subst_expr] [%e sort_expr]]
;;

let compose_subst subst_expr1 subst_expr2 =
  match use_subst with
  | true -> [%expr Subst.compose [%e subst_expr1] [%e subst_expr2]]
  | false -> [%expr Renaming.compose [%e subst_expr1] [%e subst_expr2]]
;;

let bind_expr vars_expr =
  match use_subst with
  | true -> [%expr Subst.unbind' [%e vars_expr]]
  | false -> [%expr Renaming.bind' [%e vars_expr]]
;;

let unbind_expr vars_expr =
  match use_subst with
  | true -> [%expr Subst.unbind' [%e vars_expr]]
  | false -> [%expr Renaming.unbind' [%e vars_expr]]
;;

module Walks (Config : sig
    val use_flat_names_internally : bool
    val qualify_constructors : bool
    val raise_internal_error_expr : Ppxlib.expression
  end)
=
struct
  let rec fold_map_code_for_simple_abt uniquifier ~acc (abt : [ `Simple ] Abt.t) =
    match abt with
    | Arg_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident ("f_" ^ name))
         [ (Nolabel, acc)
         ; (Nolabel, eident name')
         ])
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".fold_map"))
         (fold_map_code_for_simple_abt_args args
          @
          [ (Nolabel, acc)
          ; (Nolabel, eident name')
          ]))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_fold_map"
             | false -> String.capitalize name ^ "._fold_map"))
         (fold_map_code_for_simple_abt_args args
          @
          [ (Nolabel, acc)
          ; (Nolabel, eident name')
          ]))
    | Closed_abt_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr ([%e acc], [%e eident name])])
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, [%expr ([%e acc], [%e eident name])])
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       [%expr ([%e acc], [%e eident name])])
    | Prod abts ->
      let rec make_tuple_fold i acc abts =
        match abts with
        | [] ->
          ([],
           Exp.tuple
             [ eident "acc"
             ; Exp.tuple (List.init i ~f:(fun i -> eident (sprintf "result_%d" i)))
             ])
        | abt :: abts ->
          let (pat, expr) = fold_map_code_for_simple_abt uniquifier ~acc abt in
          let (pats, expr') = make_tuple_fold (i + 1) (eident "acc") abts in
          (pat :: pats,
           [%expr let (acc, [%p pvar (sprintf "result_%d" i)]) = [%e expr] in [%e expr']])
      in
      let (pats, expr) = make_tuple_fold 0 acc abts in
      (Pat.tuple pats, expr)

  and fold_map_code_for_simple_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) =
        fold_map_code_for_simple_abt (Uniquifier.create ()) ~acc:(eident "acc") arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (pvar "acc")
         (Exp.fun_ Nolabel None pat expr)))
  ;;

  let used_subst_of_list used_subst_list =
    (match
       List.exists used_subst_list ~f:(function
         | `Used_subst -> true
         | `Ignored_subst -> false)
     with
     | true -> `Used_subst
     | false -> `Ignored_subst)
  ;;

  let rec apply_subst_code_for_simple_abt uniquifier ~subst (abt : [ `Simple ] Abt.t) =
    match abt with
    | Arg_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident ("apply_subst_" ^ name))
         [ (Nolabel, subst)
         ; (Nolabel, eident name')
         ],
       `Used_subst)
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".apply_subst"))
         (apply_subst_code_for_simple_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_subst"
             | false -> String.capitalize name ^ "._apply_subst"))
         (apply_subst_code_for_simple_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         With_subst.apply_subst
           [%e subst]
           [%e eident name']
       ],
       `Used_subst)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, apply_subst_to_var subst (eident name), `Used_subst)
    | Sort_use name ->
      let sort_tag = String.capitalize name in
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       apply_subst_to_sort sort_tag subst (eident name),
       `Used_subst)
    | Prod abts ->
      let (pats, exprs, used_subst) =
        List.map abts ~f:(apply_subst_code_for_simple_abt uniquifier ~subst)
        |> List.unzip3
      in
      (Pat.tuple pats, Exp.tuple exprs, used_subst_of_list used_subst)

  and apply_subst_code_for_simple_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr, used_subst) =
        apply_subst_code_for_simple_abt
          (Uniquifier.create ())
          ~subst:(eident "subst")
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (match used_subst with
          | `Used_subst -> pvar "subst"
          | `Ignored_subst -> pvar "_subst")
         (Exp.fun_ Nolabel None pat expr)))
  ;;

  let rec apply_subst_code_for_open_abt uniquifier ~subst (abt : [ `Open ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".apply_subst"))
         (apply_subst_code_for_open_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_subst"
             | false -> String.capitalize name ^ "._apply_subst"))
         (apply_subst_code_for_open_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Open_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_subst"
             | false -> String.capitalize name ^ "._apply_subst"))
         ([ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         With_subst.apply_subst
           [%e subst]
           [%e eident name']
       ],
       `Used_subst)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, apply_subst_to_var subst (eident name), `Used_subst)
    | Sort_use name ->
      let sort_tag = String.capitalize name in
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       apply_subst_to_sort sort_tag subst (eident name),
       `Used_subst)
    | Prod abts ->
      let (pats, exprs, used_subst) =
        List.map abts ~f:(apply_subst_code_for_open_abt uniquifier ~subst)
        |> List.unzip3
      in
      (Pat.tuple pats, Exp.tuple exprs, used_subst_of_list used_subst)
    | Symbol_binding name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, eident name, `Ignored_subst)
    | Sort_binding name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, eident name, `Ignored_subst)

  and apply_subst_code_for_open_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr, used_subst) =
        apply_subst_code_for_open_abt
          (Uniquifier.create ())
          ~subst:(eident "subst")
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (match used_subst with
          | `Used_subst -> pvar "subst"
          | `Ignored_subst -> pvar "_subst")
         (Exp.fun_ Nolabel None pat expr)))
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
      (match args with
       | [] -> (pvar name', `Pair (`List [], eident name'))
       | _::_ ->
         (pvar name',
          `Expr
            (Exp.apply
               (eident (Builtin_abt.module_name builtin_abt ^ ".fold_map"))
               (into_code_for_open_abt_args args
                @
                [ (Nolabel, [%expr []])
                ; (Nolabel, eident name')
                ]))))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (match args with
       | [] -> (pvar name', `Pair (`List [], eident name'))
       | _::_ ->
         (pvar name',
          `Expr
            (Exp.apply
               (eident
                  (match Config.use_flat_names_internally with
                   | true -> name ^ "_fold_map"
                   | false -> String.capitalize name ^ "._fold_map"))
               (into_code_for_open_abt_args args
                @
                [ (Nolabel, [%expr []])
                ; (Nolabel, eident name')
                ]))))
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
      (pvar name,
       `Pair (`List [], eident name))
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
      (pvar name',
       `Pair
         (`List [ [%expr Packed_var.T ([%e Exp.construct (lident (String.capitalize name)) None], [%e eident name'])] ],
          [%expr Temp.name [%e eident name']]))
    | Sort_binding sort ->
      let name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
      (pvar name,
       `Pair
         (`List
            [ [%expr Packed_var.T ([%e Exp.construct (lident (String.capitalize sort)) None], [%e eident name])] ],
          [%expr Temp.name [%e eident name]]))

  and into_code_for_open_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) = into_code_for_open_abt (Uniquifier.create ()) arg in
      (Nolabel,
       Exp.fun_ Nolabel None
         (pvar "acc")
         (Exp.fun_ Nolabel None pat
            (match expr with
             | `Pair (vars_expr, abt_expr) ->
               [%expr ([%e vars_to_expr vars_expr] @ acc, [%e abt_expr])]
             | `Expr expr ->
               [%expr
                 let (vars, inner) = [%e expr] in
                 (vars @ acc, inner)
               ]))))
  ;;

  let rec into_code_for_closed_abt uniquifier subst (abt : [ `Closed ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".apply_subst"))
         (into_code_for_closed_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_subst"
             | false -> String.capitalize name ^ "._apply_subst"))
         (into_code_for_closed_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name', [%expr With_subst.apply_subst [%e subst] [%e eident name']], `Used_subst)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (* CR wduff: We need to apply the substitution in this case, but we don't current have a way
         to apply it to a symbol. *)
      (pvar name,
       [%expr Internal_var.Free_var [%e eident name]],
       `Used_subst)
    | Sort_use name ->
      let sort_tag = String.capitalize name in
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, apply_subst_to_sort sort_tag subst (eident name), `Used_subst)
    | Prod abts ->
      let (pats, exprs, used_subst) =
        List.map abts ~f:(into_code_for_closed_abt uniquifier subst)
        |> List.unzip3
      in
      (Pat.tuple pats, Exp.tuple exprs, used_subst_of_list used_subst)
    | Bind (lhs, rhs) ->
      let (lhs_pat, lhs_expr) =
        (* CR wduff: Apply the subst to the expr at some point. *)
        into_code_for_open_abt uniquifier lhs
      in
      let (rhs_pat, rhs_expr, used_subst) =
        into_code_for_closed_abt
          uniquifier
          [%expr subst]
          rhs
      in
      let expr =
        match used_subst with
        | `Used_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               let subst =
                 [%e compose_subst subst (bind_expr (vars_to_expr lhs_vars_expr))]
               in
               ([%e lhs_abt_expr], [%e rhs_expr])]
           | `Expr lhs_expr ->
             [%expr
               let (vars, lhs) = [%e lhs_expr] in
               let subst = [%e compose_subst subst (bind_expr [%expr vars])] in
               (lhs, [%e rhs_expr])
             ])
        | `Ignored_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               ignore [%e vars_to_expr lhs_vars_expr];
               ([%e lhs_abt_expr], [%e rhs_expr])]
           | `Expr lhs_expr ->
             [%expr
               let (_, lhs) = [%e lhs_expr] in
               (lhs, [%e rhs_expr])
             ])
      in
      ([%pat? ([%p lhs_pat], [%p rhs_pat])], expr, used_subst)

  and into_code_for_closed_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr, used_subst) =
        into_code_for_closed_abt
          (Uniquifier.create ())
          [%expr subst]
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (match used_subst with
          | `Used_subst -> [%pat? subst]
          | `Ignored_subst -> [%pat? _subst])
         (Exp.fun_ Nolabel None pat expr)))
  ;;

  let rec out_code_for_open_abt uniquifier (abt : [ `Open ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (match args with
       | [] -> (pvar name', `Pair (`List [], eident name'))
       | _::_ ->
         (pvar name',
          `Expr
            (Exp.apply
               (eident (Builtin_abt.module_name builtin_abt ^ ".fold_map"))
               (out_code_for_open_abt_args args
                @
                [ (Nolabel, [%expr []])
                ; (Nolabel, eident name')
                ]))))
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (match args with
       | [] -> (pvar name', `Pair (`List [], eident name'))
       | _::_ ->
         (pvar name',
          `Expr
            (Exp.apply
               (eident
                  (match Config.use_flat_names_internally with
                   | true -> name ^ "_fold_map"
                   | false -> String.capitalize name ^ "._fold_map"))
               (out_code_for_open_abt_args args
                @
                [ (Nolabel, [%expr []])
                ; (Nolabel, eident name')
                ]))))
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       `Pair (`List [], eident name'))
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
             [%e eident name']
         ])
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       `Pair
         (`List [],
          [%expr
            match [%e eident name] with
            | Internal_var.Free_var var -> var
            | Internal_var.Bound_var _ -> [%e Config.raise_internal_error_expr]]))
    | Sort_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, `Pair (`List [], eident name))
    | Prod abts ->
      let (pats, exprs) =
        List.map abts ~f:(out_code_for_open_abt uniquifier)
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
      (* CR wduff: Is there a function for getting the module name for a sort? *)
      let var_create = Exp.ident (lident (String.capitalize sort ^ ".Var.create")) in
      let bound_name = Uniquifier.uniquify uniquifier ("bound_" ^ sort ^ "_name") in
      let var_name = Uniquifier.uniquify uniquifier (sort ^ "_var") in
      (pvar bound_name,
       `Expr
         [%expr
           let [%p pvar var_name] = [%e var_create] [%e eident bound_name] in
           ([ Packed_var.T ([%e Exp.construct (lident (String.capitalize sort)) None], [%e eident var_name]) ],
            [%e eident var_name])
         ])

  and out_code_for_open_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr) = out_code_for_open_abt (Uniquifier.create ()) arg in
      (Nolabel,
       Exp.fun_ Nolabel None
         [%pat? acc]
         (Exp.fun_ Nolabel None pat
            (match expr with
             | `Pair (vars_expr, abt_expr) ->
               [%expr ([%e vars_to_expr vars_expr] @ acc, [%e abt_expr])]
             | `Expr expr ->
               [%expr
                 let (vars, outer) = [%e expr] in
                 (vars @ acc, outer)
               ]))))
;;

  let rec out_code_for_closed_abt uniquifier subst (abt : [ `Closed ] Abt.t) =
    match abt with
    | Builtin_abt_use (builtin_abt, args) ->
      let name' = Uniquifier.uniquify uniquifier (Builtin_abt.name builtin_abt) in
      (pvar name',
       Exp.apply
         (eident (Builtin_abt.module_name builtin_abt ^ ".apply_subst"))
         (out_code_for_closed_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Simple_abt_use (name, args) ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       Exp.apply
         (eident
            (match Config.use_flat_names_internally with
             | true -> name ^ "_apply_subst"
             | false -> String.capitalize name ^ "._apply_subst"))
         (out_code_for_closed_abt_args args
          @
          [ (Nolabel, subst)
          ; (Nolabel, eident name')
          ]),
       `Used_subst)
    | Closed_abt_use name ->
      let name' = Uniquifier.uniquify uniquifier name in
      (pvar name',
       [%expr
         With_subst.apply_subst
           [%e subst]
           [%e eident name']
       ],
       `Used_subst)
    | Symbol_use name ->
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name,
       [%expr
         match [%e apply_subst_to_var subst (eident name)] with
         | Internal_var.Free_var var -> var
         | Internal_var.Bound_var _ -> [%e Config.raise_internal_error_expr]
       ],
       `Used_subst)
    | Sort_use name ->
      let sort_tag = String.capitalize name in
      let name = Uniquifier.uniquify uniquifier name in
      (pvar name, apply_subst_to_sort sort_tag subst (eident name), `Used_subst)
    | Prod abts ->
      let (pats, exprs, used_subst) =
        List.map abts
          ~f:(out_code_for_closed_abt
                uniquifier
                subst)
        |> List.unzip3
      in
      (Pat.tuple pats, Exp.tuple exprs, used_subst_of_list used_subst)
    | Bind (lhs, rhs) ->
      let (lhs_pat, lhs_expr) = out_code_for_open_abt uniquifier lhs in
      let (lhs_pat', lhs_expr', lhs_used_subst) =
        apply_subst_code_for_open_abt uniquifier ~subst lhs
      in
      let (rhs_pat, rhs_expr, rhs_used_subst) =
        out_code_for_closed_abt
          uniquifier
          [%expr subst]
          rhs
      in
      (* CR wduff: Simplify this... *)
      let expr =
        match lhs_used_subst, rhs_used_subst with
        | `Used_subst, `Used_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               let [%p lhs_pat'] = [%e lhs_abt_expr] in
               let subst =
                 [%e compose_subst subst (unbind_expr (vars_to_expr lhs_vars_expr))]
               in
               ([%e lhs_expr'], [%e rhs_expr])
             ]
           | `Expr lhs_expr ->
             [%expr
               let (vars, lhs) = [%e lhs_expr] in
               let [%p lhs_pat'] = lhs in
               let subst = [%e compose_subst subst (unbind_expr [%expr vars])] in
               ([%e lhs_expr'], [%e rhs_expr])
             ])
        | `Ignored_subst, `Used_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               let subst =
                 [%e compose_subst subst (unbind_expr (vars_to_expr lhs_vars_expr))]
               in
               ([%e lhs_abt_expr], [%e rhs_expr])
             ]
           | `Expr lhs_expr ->
             [%expr
               let (vars, lhs) = [%e lhs_expr] in
               let subst = [%e compose_subst subst (unbind_expr [%expr vars])] in
               (lhs, [%e rhs_expr])
             ])
        | `Used_subst, `Ignored_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               ignore [%e vars_to_expr lhs_vars_expr];
               let [%p lhs_pat'] = [%e lhs_abt_expr] in
               ([%e lhs_expr'], [%e rhs_expr])
             ]
           | `Expr lhs_expr ->
             [%expr
               let (_, lhs) = [%e lhs_expr] in
               let [%p lhs_pat'] = lhs in
               ([%e lhs_expr'], [%e rhs_expr])
             ])
        | `Ignored_subst, `Ignored_subst ->
          (match lhs_expr with
           | `Pair (lhs_vars_expr, lhs_abt_expr) ->
             [%expr
               ignore [%e vars_to_expr lhs_vars_expr];
               ([%e lhs_abt_expr], [%e rhs_expr])
             ]
           | `Expr lhs_expr ->
             [%expr
               let (_, lhs) = [%e lhs_expr] in
               (lhs, [%e rhs_expr])
             ])
      in
      ([%pat? ([%p lhs_pat], [%p rhs_pat])],
       expr,
       used_subst_of_list [ lhs_used_subst; rhs_used_subst ])


  and out_code_for_closed_abt_args args =
    List.map args ~f:(fun arg ->
      let (pat, expr, used_subst) =
        out_code_for_closed_abt
          (Uniquifier.create ())
          [%expr subst]
          arg
      in
      (Nolabel,
       Exp.fun_ Nolabel None
         (match used_subst with
          | `Used_subst -> [%pat? subst]
          | `Ignored_subst -> [%pat? _subst])
         (Exp.fun_ Nolabel None pat expr)))
  ;;

  let fold_map_code_for_simple_cases ~acc cases =
    List.map cases ~f:(fun (constructor_name, abt_opt) ->
      let (pat, expr) =
        match abt_opt with
        | None ->
          (Pat.construct (lident constructor_name) None,
           Exp.tuple
             [ eident "acc"
             ; Exp.construct (lident constructor_name) None
             ])
        | Some abt ->
          let (pat, expr) = fold_map_code_for_simple_abt (Uniquifier.create ()) ~acc abt in
          (Pat.construct (lident constructor_name) (Some pat),
           [%expr
             let (acc, args) = [%e expr] in
             (acc,
              [%e
                Exp.construct
                  (lident constructor_name)
                  (Some (eident "args"))
              ])
           ])
      in
      Exp.case pat expr)
  ;;

  let apply_subst_code_for_simple_cases ~subst cases =
    let (cases, used_subst) =
      List.map cases ~f:(fun (constructor_name, abt_opt) ->
        let (pat, expr, used_subst) =
          match abt_opt with
          | None ->
            (Pat.construct (lident constructor_name) None,
             Exp.construct (lident constructor_name) None,
             `Ignored_subst)
          | Some abt ->
            let (pat, expr, used_subst) =
              apply_subst_code_for_simple_abt
                (Uniquifier.create ())
                ~subst
                abt
            in
            (Pat.construct (lident constructor_name) (Some pat),
             Exp.construct (lident constructor_name) (Some expr),
             used_subst)
        in
        (Exp.case pat expr, used_subst))
      |> List.unzip
    in
    (cases, used_subst_of_list used_subst)
  ;;

  let apply_subst_code_for_open_cases ~subst cases =
    let (cases, used_subst) =
      List.map cases ~f:(fun (constructor_name, abt_opt) ->
        let (pat, expr, used_subst) =
          match abt_opt with
          | None ->
            (Pat.construct (lident constructor_name) None,
             Exp.construct (lident constructor_name) None,
             `Ignored_subst)
          | Some abt ->
            let (pat, expr, used_subst) =
              apply_subst_code_for_open_abt
                (Uniquifier.create ())
                ~subst
                abt
            in
            (Pat.construct (lident constructor_name) (Some pat),
             Exp.construct (lident constructor_name) (Some expr),
             used_subst)
        in
        (Exp.case pat expr, used_subst))
      |> List.unzip
    in
    (cases, used_subst_of_list used_subst)
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
            into_code_for_open_abt (Uniquifier.create ()) abt
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
          let (pat, expr, _used_subst) =
            into_code_for_closed_abt
              (Uniquifier.create ())
              [%expr Subst.ident]
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
            out_code_for_open_abt (Uniquifier.create ()) abt
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

  let out_code_for_closed_cases ~name_of_walked_value ~subst cases =
    let (cases, used_subst) =
      List.map cases ~f:(fun (constructor_name, abt) ->
        let (pat, expr, used_subst) =
          match abt with
          | None ->
            (None, None, `Ignored_subst)
          | Some abt ->
            let (pat, expr, used_subst) =
              out_code_for_closed_abt (Uniquifier.create ()) subst abt
            in
            (Some pat, Some expr, used_subst)
        in
        (Exp.case
           (Pat.construct
              (lident (make_internal_constructor_name ~name_of_walked_value ~constructor_name))
              pat)
           (Exp.construct (lident constructor_name) expr),
         used_subst))
      |> List.unzip
    in
    (cases, used_subst_of_list used_subst)
  ;;

  (* CR wduff Remove the below after converting the SML. *)
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
      | Open_abt_use name ->
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
      | Closed_abt_use name | Sort_use name ->
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
