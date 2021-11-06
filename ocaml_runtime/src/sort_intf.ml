open! Base

module type S = sig
  type ('var, 'sort) t

  val same_witness
    :  ('var1, 'sort1) t
    -> ('var2, 'sort2) t
    -> (('var1, 'var2) Type_equal.t * ('sort1, 'sort2) Type_equal.t) option
end
