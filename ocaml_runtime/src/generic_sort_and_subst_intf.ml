open! Base

module type S = sig
  type ('var, 'sort) sort

  module Packed_var : sig
    type t = T : ('var, _) sort * 'var -> t
  end

  module rec Generic_sort : sig
    type ('var, 'oper) t = private
      | Var of 'var Internal_var.t
      | Oper of Subst.t * 'oper

    val var : 'var -> ('var, _) t
    val oper : 'oper -> (_, 'oper) t

    val apply_subst : ('var, ('var, 'oper) t) sort -> Subst.t -> ('var, 'oper) t -> ('var, 'oper) t
  end

  and With_subst : sig
    type 'a t = Subst.t * 'a

    val apply_subst : Subst.t -> 'a t -> 'a t
  end

  and Subst : sig
    type t

    val apply_to_var
      : t -> ('var, ('var, 'oper) Generic_sort.t) sort -> 'var Internal_var.t -> ('var, 'oper) Generic_sort.t

    val ident : t
    val compose : t -> t -> t

    val singleton : ('var, 'sort) sort -> 'sort -> 'var -> t

    val bind : ('var, _) sort -> 'var -> t
    val bind' : Packed_var.t list -> t

    val unbind : ('var, _) sort -> 'var -> t
    val unbind' : Packed_var.t list -> t
  end
end

module type Generic_sort_and_subst = sig
  module type S = S

  module Make (Sort : Sort_intf.S) : S with type ('var, 'sort) sort := ('var, 'sort) Sort.t
end
