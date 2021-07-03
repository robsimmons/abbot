open! Core
open! Abbot_runtime
open! System_f_intf

module Typ_var : Temp_intf.S = Temp
module Term_var : Temp_intf.S = Temp

module rec Typ : sig
  module Var = Typ_var

  type oper
  type t = (Var.t, oper) GSS.Generic_sort.t [@@deriving sexp_of]

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
end = struct
  open GSS

  module Var = Typ_var

  type view =
    | Var of Typ.Var.t
    | Arrow of (Typ.t * Typ.t)
    | Forall of (Typ.Var.t, Typ.t) bind
  [@@deriving sexp_of]

  type oper =
    | Arrow of (Typ.t * Typ.t)
    | Forall of (string compare_ignore, Typ.t) bind
  type t = (Var.t, oper) Generic_sort.t

  let into (view : view) : t =
    match view with
    | Var var -> Generic_sort.var var
    | Arrow (typ1, typ2) ->
      Generic_sort.oper
        (Arrow
           (Generic_sort.apply_subst Typ Subst.ident typ1,
            Generic_sort.apply_subst Typ Subst.ident typ2))
    | Forall (typ_var1, typ1) ->
      let subst = Subst.compose Subst.ident (Subst.bind' [ T (Typ, typ_var1) ]) in
      Generic_sort.oper
        (Forall (Typ.Var.name typ_var1, Generic_sort.apply_subst Typ subst typ1))
  ;;

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (subst, oper) ->
      (match oper with
       | Arrow (typ1, typ2) ->
         Arrow
           (Generic_sort.apply_subst Typ subst typ1,
            Generic_sort.apply_subst Typ subst typ2)
       | Forall (bound_typ_name1, typ1) ->
         let typ_var1 = Typ.Var.create bound_typ_name1 in
         let subst = Subst.compose subst (Subst.unbind' [ T (Typ, typ_var1) ]) in
         Forall (typ_var1, Generic_sort.apply_subst Typ subst typ1))
  ;;

  let var arg = into (Var arg)
  let arrow arg = into (Arrow arg)
  let forall arg = into (Forall arg)
  let sexp_of_t t = [%sexp_of: view] (out t)

  let subst (type var) (type sort) (sort : (var, sort) Sort.t) (value : sort) (var : var) (t : t) : t =
    let module T = struct type t = T : ((var, _) Generic_sort.t, sort) Type_equal.t -> t end in
    let (T T) =
      match sort with
      | Typ -> T.T T
      | Term -> T.T T
    in
    Generic_sort.apply_subst Typ (Subst.singleton sort value var) t
  ;;
end

and Term : sig
  module Var = Term_var

  type oper
  type t = (Var.t, oper) GSS.Generic_sort.t [@@deriving sexp_of]

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
end = struct
  open GSS

  module Var = Term_var

  type view =
    | Var of Term.Var.t
    | Fun of (Term.Var.t * Typ.t, Term.t) bind
    | Ap of (Term.t * Term.t)
    | TypFun of (Typ.Var.t, Term.t) bind
    | TypAp of (Term.t * Typ.t)
  [@@deriving sexp_of]

  type oper =
    | Fun of (string compare_ignore * Typ.t, Term.t) bind
    | Ap of (Term.t * Term.t)
    | TypFun of (string compare_ignore, Term.t) bind
    | TypAp of (Term.t * Typ.t)
  type t = (Var.t, oper) Generic_sort.t

  let into (view : view) : t =
    match view with
    | Var var -> Generic_sort.var var
    | Fun ((term_var1, typ1), term1) ->
      let subst =
        Subst.compose Subst.ident (Subst.bind' [ T (Term, term_var1) ])
      in
      Generic_sort.oper
        (Fun
           ((Term.Var.name term_var1,
             Generic_sort.apply_subst Typ Subst.ident typ1),
            Generic_sort.apply_subst Term subst term1))
    | Ap (term1, term2) ->
      Generic_sort.oper
        (Ap
           (Generic_sort.apply_subst Term Subst.ident term1,
            Generic_sort.apply_subst Term Subst.ident term2))
    | TypFun (typ_var1, term1) ->
      let subst = Subst.compose Subst.ident (Subst.bind' [ T (Typ, typ_var1) ]) in
      Generic_sort.oper
        (TypFun (Typ.Var.name typ_var1, Generic_sort.apply_subst Term subst term1))
    | TypAp (term1, typ1) ->
      Generic_sort.oper
        (TypAp
           (Generic_sort.apply_subst Term Subst.ident term1,
            Generic_sort.apply_subst Typ Subst.ident typ1))
  ;;

  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (subst, oper) ->
      (match oper with
       | Fun ((bound_term_name1, typ1), term1) ->
         let term_var1 = Term.Var.create bound_term_name1 in
         let lhs = (term_var1, Generic_sort.apply_subst Typ subst typ1) in
         let subst = Subst.compose subst (Subst.unbind' [ T (Term, term_var1) ]) in
         Fun (lhs, Generic_sort.apply_subst Term subst term1)
       | Ap (term1, term2) ->
         Ap
           (Generic_sort.apply_subst Term subst term1,
            Generic_sort.apply_subst Term subst term2)
       | TypFun (bound_typ_name1, term1) ->
         let typ_var1 = Typ.Var.create bound_typ_name1 in
         let subst = Subst.compose subst (Subst.unbind' [ T (Typ, typ_var1) ]) in
         TypFun (typ_var1, Generic_sort.apply_subst Term subst term1)
       | TypAp (term1, typ1) ->
         TypAp
           (Generic_sort.apply_subst Term subst term1,
            Generic_sort.apply_subst Typ subst typ1))
  ;;

  let var arg = into (Var arg)
  let fun_ arg = into (Fun arg)
  let ap arg = into (Ap arg)
  let typfun arg = into (TypFun arg)
  let typap arg = into (TypAp arg)
  let sexp_of_t t = [%sexp_of: view] (out t)

  let subst (type var) (type sort) (sort : (var, sort) Sort.t) (value : sort) (var : var) (t : t) : t =
    let module T = struct type t = T : ((var, _) Generic_sort.t, sort) Type_equal.t -> t end in
    let (T T) =
      match sort with
      | Typ -> T.T T
      | Term -> T.T T
    in
    Generic_sort.apply_subst Term (Subst.singleton sort value var) t
  ;;
end

and Sort : sig
  type (_, _) t = Typ : (Typ.Var.t, Typ.t) t | Term : (Term.Var.t, Term.t) t

  include Sort_intf.S with type ('var, 'sort) t := ('var, 'sort) t
end = struct
  type (_, _) t = Typ : (Typ.Var.t, Typ.t) t | Term : (Term.Var.t, Term.t) t

  let same_witness
        (type var1)
        (type sort1)
        (type var2)
        (type sort2)
        (t1 : (var1, sort1) t)
        (t2 : (var2, sort2) t)
    : ((var1, var2) Type_equal.t * (sort1, sort2) Type_equal.t) option =
    match (t1, t2) with
    | (Typ, Typ) -> Some (T, T)
    | (Term, Term) -> Some (T, T)
    | _ -> None
end

and GSS
  : Generic_sort_and_subst.S with type ('var, 'sort) sort := ('var, 'sort) Sort.t =
  Generic_sort_and_subst.Make (Sort)
