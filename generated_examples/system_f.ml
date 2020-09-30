open! Core
open! Abbot_runtime
open! System_f_intf
module rec Typ :
  sig
    type oper
    type t = oper Internal_sort.t [@@deriving sexp_of]
    module Var = Temp
    type view =
      | Var of Typ.Var.t
      | Arrow of (Typ.t * Typ.t)
      | Forall of (Typ.Var.t, Typ.t) bind
    [@@deriving sexp_of]
    val var : Var.t -> t
    val arrow : Typ.t * Typ.t -> t
    val forall : (Typ.Var.t, Typ.t) bind -> t
    val into : view -> t
    val out : t -> view
    val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
  end
=
struct
  module Var = Temp
  type oper =
    | Arrow of (Typ.t * Typ.t)
    | Forall of (string compare_ignore, Typ.t) bind
  type t = oper Internal_sort.t
  type view =
    | Var of Typ.Var.t
    | Arrow of (Typ.t * Typ.t)
    | Forall of (Typ.Var.t, Typ.t) bind
  [@@deriving sexp_of]
  let into (view : view) : t =
    match view with
    | Var var -> Var (Free_var var)
    | Arrow (typ1, typ2) ->
      Oper
        (
          Renaming.ident
        ,
          Arrow
            (
              Internal_sort.apply_renaming Subst.ident typ1
            ,
              Internal_sort.apply_renaming Subst.ident typ2
            )
        )
    | Forall (typ_var1, typ1) ->
      Oper
        (
          Renaming.ident
        ,
          Forall
            (
            let renaming =
              Renaming.compose Subst.ident (Renaming.bind' [ typ_var1 ])
            in
            (Temp.name typ_var1, Internal_sort.apply_renaming renaming typ1))
        )
  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      (match oper with
      | Arrow (typ1, typ2) ->
        Arrow
          (
            Internal_sort.apply_renaming renaming typ1
          ,
            Internal_sort.apply_renaming renaming typ2
          )
      | Forall (bound_typ_name1, typ1) ->
        Forall
          (
          let (vars, lhs) =
            let typ_var1 = Temp.create bound_typ_name1 in
            ([ typ_var1 ], typ_var1)
          in
          let renaming = Renaming.compose renaming (Renaming.unbind' vars) in
          (lhs, Internal_sort.apply_renaming renaming typ1)
          )
      )
  let var arg = into (Var arg)
  let arrow arg = into (Arrow arg)
  let forall arg = into (Forall arg)
  let sexp_of_t t = [%sexp_of: view] (out t)
  let subst =
    (fun
      (type var)
      (type sort)
      (sort : (var, sort) Sort.t)
      (value : sort)
      (var : var)
      (t : t)
    ->
      (
        match out t with
        | Var var' ->
          (match sort with
          | Sort.Typ ->
            (match Temp.equal var var' with | true -> value | false -> t)
          | _ -> t
          )
        | Arrow (typ1, typ2) ->
          Arrow (Typ.subst sort value var typ1, Typ.subst sort value var typ2)
          |>
            into
        | Forall (typ_var1, typ1) ->
          Forall (typ_var1, Typ.subst sort value var typ1) |> into
        : t)
    )
end
and Term :
  sig
    type oper
    type t = oper Internal_sort.t [@@deriving sexp_of]
    module Var = Temp
    type view =
      | Var of Term.Var.t
      | Fun of (Term.Var.t * Typ.t, Term.t) bind
      | Ap of (Term.t * Term.t)
      | TypFun of (Typ.Var.t, Term.t) bind
      | TypAp of (Term.t * Typ.t)
    [@@deriving sexp_of]
    val var : Var.t -> t
    val fun_ : (Term.Var.t * Typ.t, Term.t) bind -> t
    val ap : Term.t * Term.t -> t
    val typfun : (Typ.Var.t, Term.t) bind -> t
    val typap : Term.t * Typ.t -> t
    val into : view -> t
    val out : t -> view
    val subst : ('var, 'sort) Sort.t -> 'sort -> 'var -> t -> t
  end
=
struct
  module Var = Temp
  type oper =
    | Fun of (string compare_ignore * Typ.t, Term.t) bind
    | Ap of (Term.t * Term.t)
    | TypFun of (string compare_ignore, Term.t) bind
    | TypAp of (Term.t * Typ.t)
  type t = oper Internal_sort.t
  type view =
    | Var of Term.Var.t
    | Fun of (Term.Var.t * Typ.t, Term.t) bind
    | Ap of (Term.t * Term.t)
    | TypFun of (Typ.Var.t, Term.t) bind
    | TypAp of (Term.t * Typ.t)
  [@@deriving sexp_of]
  let into (view : view) : t =
    match view with
    | Var var -> Var (Free_var var)
    | Fun ((term_var1, typ1), term1) ->
      Oper
        (
          Renaming.ident
        ,
          Fun
            (
            let renaming =
              Renaming.compose Subst.ident (Renaming.bind' [ term_var1 ])
            in
            (
              (
                Temp.name term_var1
              ,
                Internal_sort.apply_renaming Subst.ident typ1
              )
            ,
              Internal_sort.apply_renaming renaming term1
            )
            )
        )
    | Ap (term1, term2) ->
      Oper
        (
          Renaming.ident
        ,
          Ap
            (
              Internal_sort.apply_renaming Subst.ident term1
            ,
              Internal_sort.apply_renaming Subst.ident term2
            )
        )
    | TypFun (typ_var1, term1) ->
      Oper
        (
          Renaming.ident
        ,
          TypFun
            (
            let renaming =
              Renaming.compose Subst.ident (Renaming.bind' [ typ_var1 ])
            in
            (Temp.name typ_var1, Internal_sort.apply_renaming renaming term1))
        )
    | TypAp (term1, typ1) ->
      Oper
        (
          Renaming.ident
        ,
          TypAp
            (
              Internal_sort.apply_renaming Subst.ident term1
            ,
              Internal_sort.apply_renaming Subst.ident typ1
            )
        )
  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (renaming, oper) ->
      (match oper with
      | Fun ((bound_term_name1, typ1), term1) ->
        Fun
          (
          let (vars, lhs) =
            let (vars_0, outer_0) =
              let term_var1 = Temp.create bound_term_name1 in
              ([ term_var1 ], term_var1)
            in
            (vars_0, (outer_0, Internal_sort.apply_renaming renaming typ1))
          in
          let renaming = Renaming.compose renaming (Renaming.unbind' vars) in
          (lhs, Internal_sort.apply_renaming renaming term1)
          )
      | Ap (term1, term2) ->
        Ap
          (
            Internal_sort.apply_renaming renaming term1
          ,
            Internal_sort.apply_renaming renaming term2
          )
      | TypFun (bound_typ_name1, term1) ->
        TypFun
          (
          let (vars, lhs) =
            let typ_var1 = Temp.create bound_typ_name1 in
            ([ typ_var1 ], typ_var1)
          in
          let renaming = Renaming.compose renaming (Renaming.unbind' vars) in
          (lhs, Internal_sort.apply_renaming renaming term1)
          )
      | TypAp (term1, typ1) ->
        TypAp
          (
            Internal_sort.apply_renaming renaming term1
          ,
            Internal_sort.apply_renaming renaming typ1
          )
      )
  let var arg = into (Var arg)
  let fun_ arg = into (Fun arg)
  let ap arg = into (Ap arg)
  let typfun arg = into (TypFun arg)
  let typap arg = into (TypAp arg)
  let sexp_of_t t = [%sexp_of: view] (out t)
  let subst =
    (fun
      (type var)
      (type sort)
      (sort : (var, sort) Sort.t)
      (value : sort)
      (var : var)
      (t : t)
    ->
      (
        match out t with
        | Var var' ->
          (match sort with
          | Sort.Term ->
            (match Temp.equal var var' with | true -> value | false -> t)
          | _ -> t
          )
        | Fun ((term_var1, typ1), term1) ->
          Fun
            (
              (term_var1, Typ.subst sort value var typ1)
            ,
              Term.subst sort value var term1
            )
          |>
            into
        | Ap (term1, term2) ->
          Ap (Term.subst sort value var term1, Term.subst sort value var term2)
          |>
            into
        | TypFun (typ_var1, term1) ->
          TypFun (typ_var1, Term.subst sort value var term1) |> into
        | TypAp (term1, typ1) ->
          TypAp (Term.subst sort value var term1, Typ.subst sort value var typ1)
          |>
            into
        : t)
    )
end
and Sort :
  sig
    type (_, _) t = Typ : (Typ.Var.t, Typ.t) t | Term : (Term.Var.t, Term.t) t
  end
=
struct
  type (_, _) t = Typ : (Typ.Var.t, Typ.t) t | Term : (Term.Var.t, Term.t) t
end
