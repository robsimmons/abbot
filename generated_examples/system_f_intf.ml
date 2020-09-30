open! Core
open! Abbot_runtime
type ('a, 'b) bind = 'a * 'b [@@deriving compare, sexp]
module type System_f = sig
  module rec Typ : sig
    type t [@@deriving sexp_of]
    module Var : Temp_intf.S
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
  and Term : sig
    type t [@@deriving sexp_of]
    module Var : Temp_intf.S
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
  and Sort : sig
    type (_, _) t = Typ : (Typ.Var.t, Typ.t) t | Term : (Term.Var.t, Term.t) t
  end
end
