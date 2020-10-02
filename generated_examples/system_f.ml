open! Core
open! Abbot_runtime
open! System_f_intf

let raise_not_fresh var =
  raise_s
    [%message
      "Internal abbot bug. Variable passed to [unbind] was not fresh."
        (var : Temp.t)]
;;

module type Sort = sig
  type ('var, 'sort) t

  val same_witness
    :  ('var1, 'sort1) t
    -> ('var2, 'sort2) t
    -> (('var1, 'var2) Type_equal.t * ('sort1, 'sort2) Type_equal.t) option
end

module type Foo = sig
  type ('var, 'sort) sort

  module rec Internal_sort : sig
    type 'oper t = (* CR wduff: This should be private, but [Subst] needs to see the internals. *)
      | Var of Internal_var.t
      | Oper of Subst.t * 'oper

    val var : Temp.t -> _ t
    val oper : 'oper -> 'oper t

    val apply_subst : ('var, 'oper t) sort -> Subst.t -> 'oper t -> 'oper t
  end

  and Subst : sig
    type t

    val apply_to_var
      : t -> ('var, 'oper Internal_sort.t) sort -> Internal_var.t -> 'oper Internal_sort.t

    val ident : t
    val compose : t -> t -> t

    val singleton : ('var, 'oper Internal_sort.t) sort -> 'oper Internal_sort.t -> Temp.t -> t

    val bind : Temp.t -> t
    val bind' : Temp.t list -> t

    val unbind : Temp.t -> t
    val unbind' : Temp.t list -> t
  end
end

module Make_foo (Sort : Sort) : Foo with type ('var, 'sort) sort := ('var, 'sort) Sort.t = struct
  module rec Internal_sort : sig
    type 'oper t = (* CR wduff: This should be private, but [Subst] needs to see the internals. *)
      | Var of Internal_var.t
      | Oper of Subst.t * 'oper

    val var : Temp.t -> _ t
    val oper : 'oper -> 'oper t

    val apply_subst : ('var, 'oper t) Sort.t -> Subst.t -> 'oper t -> 'oper t
  end = struct
    type 'oper t =
      | Var of Internal_var.t
      | Oper of Subst.t * 'oper

    let var x = Var (Free_var x)
    let oper oper = Oper (Subst.ident, oper)

    let apply_subst sort subst = function
      | Var var -> Subst.apply_to_var subst sort var
      | Oper (subst', oper) -> Oper (Subst.compose subst subst', oper)
    ;;
  end

  and Subst : sig
    type t

    val apply_to_var
      : t -> ('var, 'oper Internal_sort.t) Sort.t -> Internal_var.t -> 'oper Internal_sort.t

    val ident : t
    val compose : t -> t -> t

    val singleton : ('var, 'oper Internal_sort.t) Sort.t -> 'oper Internal_sort.t -> Temp.t -> t

    val bind : Temp.t -> t
    val bind' : Temp.t list -> t

    val unbind : Temp.t -> t
    val unbind' : Temp.t list -> t
  end = struct
    type t =
      | Ident
      | Fun of { f : 'var 'oper. ('var, 'oper Internal_sort.t) Sort.t -> Internal_var.t -> 'oper Internal_sort.t }

    let apply_to_var t sort var : _ Internal_sort.t =
      match t with
      | Ident -> Var var
      | Fun { f } -> f sort var
    ;;

    let ident = Ident

    let compose t1 t2 =
      match (t1, t2) with
      | Ident, t | t, Ident -> t
      | Fun _, Fun { f = f2 } ->
        Fun { f = fun sort var ->
          Internal_sort.apply_subst sort t1 (f2 sort var)
        }
    ;;

    let singleton'
          (type var oper)
          (sort : (var, oper Internal_sort.t) Sort.t)
          (value : oper Internal_sort.t)
          (free_var : Temp.t)
          (type var' oper')
          (sort' : (var', oper' Internal_sort.t) Sort.t)
          (var : Internal_var.t)
      : oper' Internal_sort.t =
      match Sort.same_witness sort sort' with
      | None -> Var var
      | Some (_, T) ->
        match var with
        | Bound_var bound_var -> Var (Bound_var bound_var)
        | Free_var free_var' ->
          match Temp.equal free_var free_var' with
          | true -> (value : oper' Internal_sort.t)
          | false -> Var (Free_var free_var')

    let singleton sort value free_var =
      Fun { f = fun sort' var -> singleton' sort value free_var sort' var }
    ;;

    let bind_internal free_var : Internal_var.t -> Internal_var.t = function
      | Bound_var bound_var -> Bound_var (bound_var + 1)
      | Free_var free_var' ->
        match Temp.equal free_var free_var' with
        | true -> Bound_var 0
        | false -> Free_var free_var'
    ;;

    let bind free_var =
      Fun { f = fun _ var -> Var (bind_internal free_var var) }

    let bind' free_vars =
      List.fold free_vars ~init:ident ~f:(fun acc free_var ->
        compose (bind free_var) acc)
    ;;

    let unbind_internal free_var : Internal_var.t -> Internal_var.t = function
      | Free_var free_var' ->
        (match Temp.equal free_var free_var' with
         | false -> Free_var free_var'
         | true -> raise_not_fresh free_var)
      | Bound_var bound_var ->
        match bound_var with
        | 0 -> Free_var free_var
        | _ -> Bound_var (bound_var - 1)
    ;;

    let unbind free_var : t =
      Fun { f = fun _ var -> Var (unbind_internal free_var var) }
    ;;

    let unbind' free_vars =
      List.fold free_vars ~init:ident ~f:(fun acc free_var -> compose acc (unbind free_var))
    ;;
  end
end

module rec Typ : sig
  type oper
  type t = oper Foo.Internal_sort.t [@@deriving sexp_of]
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
  val subst : ('var, 'sort) Sort.t -> 'sort -> Temp.t -> t -> t
end = struct
  module Var = Temp
  type view =
    | Var of Typ.Var.t
    | Arrow of (Typ.t * Typ.t)
    | Forall of (Typ.Var.t, Typ.t) bind
  [@@deriving sexp_of]
  type oper =
    | Arrow of (Typ.t * Typ.t)
    | Forall of (string compare_ignore, Typ.t) bind
  type t = oper Foo.Internal_sort.t
  let into (view : view) : t =
    match view with
    | Var var -> Foo.Internal_sort.var var
    | Arrow (typ1, typ2) ->
      Foo.Internal_sort.oper
        (Arrow
           (Foo.Internal_sort.apply_subst Typ Foo.Subst.ident typ1,
            Foo.Internal_sort.apply_subst Typ Foo.Subst.ident typ2))
    | Forall (typ_var1, typ1) ->
      let subst =
        Foo.Subst.compose Foo.Subst.ident (Foo.Subst.bind' [ typ_var1 ])
      in
      Foo.Internal_sort.oper
        (Forall (Temp.name typ_var1, Foo.Internal_sort.apply_subst Typ subst typ1))
  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (subst, oper) ->
      (match oper with
       | Arrow (typ1, typ2) ->
         Arrow
           (Foo.Internal_sort.apply_subst Typ subst typ1,
            Foo.Internal_sort.apply_subst Typ subst typ2)
       | Forall (bound_typ_name1, typ1) ->
         Forall
           (
             let (vars, lhs) =
               let typ_var1 = Temp.create bound_typ_name1 in
               ([ typ_var1 ], typ_var1)
             in
             let subst = Foo.Subst.compose subst (Foo.Subst.unbind' vars) in
             (lhs, Foo.Internal_sort.apply_subst Typ subst typ1)
           )
      )
  let var arg = into (Var arg)
  let arrow arg = into (Arrow arg)
  let forall arg = into (Forall arg)
  let sexp_of_t t = [%sexp_of: view] (out t)
  let subst (type var sort) (sort : (var, sort) Sort.t) (value : sort) (var : Temp.t) (t : t) : t =
    let module T = struct type t = T : (_ Foo.Internal_sort.t, sort) Type_equal.t -> t end in
    let (T T) =
      match sort with
      | Typ -> T.T T
      | Term -> T.T T
    in
    Foo.Internal_sort.apply_subst Typ (Foo.Subst.singleton sort value var) t
  ;;
end

and Term : sig
  type oper
  type t = oper Foo.Internal_sort.t [@@deriving sexp_of]
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
  val subst : ('var, 'sort) Sort.t -> 'sort -> Temp.t -> t -> t
end = struct
  module Var = Temp
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
  type t = oper Foo.Internal_sort.t
  let into (view : view) : t =
    match view with
    | Var var -> Foo.Internal_sort.var var
    | Fun ((term_var1, typ1), term1) ->
      let subst =
        Foo.Subst.compose Foo.Subst.ident (Foo.Subst.bind' [ term_var1 ])
      in
      Foo.Internal_sort.oper
        (Fun
           ((Temp.name term_var1,
             Foo.Internal_sort.apply_subst Typ Foo.Subst.ident typ1),
            Foo.Internal_sort.apply_subst Term subst term1))
    | Ap (term1, term2) ->
      Foo.Internal_sort.oper
        (Ap
           (Foo.Internal_sort.apply_subst Term Foo.Subst.ident term1,
            Foo.Internal_sort.apply_subst Term Foo.Subst.ident term2))
    | TypFun (typ_var1, term1) ->
      let subst =
        Foo.Subst.compose Foo.Subst.ident (Foo.Subst.bind' [ typ_var1 ])
      in
      Foo.Internal_sort.oper
        (TypFun (Temp.name typ_var1, Foo.Internal_sort.apply_subst Term subst term1))
    | TypAp (term1, typ1) ->
      Foo.Internal_sort.oper
        (TypAp
           (Foo.Internal_sort.apply_subst Term Foo.Subst.ident term1,
            Foo.Internal_sort.apply_subst Typ Foo.Subst.ident typ1))
  let out (t : t) : view =
    match t with
    | Var (Bound_var _) ->
      failwith "Internal Abbot error occurred. Please report this bug."
    | Var (Free_var var) -> Var var
    | Oper (subst, oper) ->
      (match oper with
       | Fun ((bound_term_name1, typ1), term1) ->
         Fun
           (
             let (vars, lhs) =
               let (vars_0, outer_0) =
                 let term_var1 = Temp.create bound_term_name1 in
                 ([ term_var1 ], term_var1)
               in
               (vars_0, (outer_0, Foo.Internal_sort.apply_subst Typ subst typ1))
             in
             let subst = Foo.Subst.compose subst (Foo.Subst.unbind' vars) in
             (lhs, Foo.Internal_sort.apply_subst Term subst term1)
           )
       | Ap (term1, term2) ->
         Ap
           (
             Foo.Internal_sort.apply_subst Term subst term1
             ,
             Foo.Internal_sort.apply_subst Term subst term2
           )
       | TypFun (bound_typ_name1, term1) ->
         TypFun
           (
             let (vars, lhs) =
               let typ_var1 = Temp.create bound_typ_name1 in
               ([ typ_var1 ], typ_var1)
             in
             let subst = Foo.Subst.compose subst (Foo.Subst.unbind' vars) in
             (lhs, Foo.Internal_sort.apply_subst Term subst term1)
           )
       | TypAp (term1, typ1) ->
         TypAp
           (
             Foo.Internal_sort.apply_subst Term subst term1
             ,
             Foo.Internal_sort.apply_subst Typ subst typ1
           )
      )
  let var arg = into (Var arg)
  let fun_ arg = into (Fun arg)
  let ap arg = into (Ap arg)
  let typfun arg = into (TypFun arg)
  let typap arg = into (TypAp arg)
  let sexp_of_t t = [%sexp_of: view] (out t)
  let subst (type var sort) (sort : (var, sort) Sort.t) (value : sort) (var : Temp.t) (t : t) : t =
    let module T = struct type t = T : (_ Foo.Internal_sort.t, sort) Type_equal.t -> t end in
    let (T T) =
      match sort with
      | Typ -> T.T T
      | Term -> T.T T
    in
    Foo.Internal_sort.apply_subst Term (Foo.Subst.singleton sort value var) t
  ;;
end

and Sort : sig
  type ('var, 'sort) t =
    | Typ : (Typ.Var.t, Typ.t) t
    | Term : (Term.Var.t, Term.t) t

  include Sort with type ('var, 'sort) t := ('var, 'sort) t
end = struct
  type ('var, 'sort) t =
    | Typ : (Typ.Var.t, Typ.t) t
    | Term : (Term.Var.t, Term.t) t

  let same_witness
        (type var1 sort1 var2 sort2)
        (t1 : (var1, sort1) t)
        (t2 : (var2, sort2) t)
    : ((var1, var2) Type_equal.t * (sort1, sort2) Type_equal.t) option =
    match (t1, t2) with
    | Typ, Typ -> Some (T, T)
    | Term, Term -> Some (T, T)
    | _ -> None
end

and Foo : Foo with type ('var, 'sort) sort := ('var, 'sort) Sort.t = Make_foo (Sort)
