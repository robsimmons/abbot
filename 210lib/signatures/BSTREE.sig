signature BSTREE =
sig
  structure Key : ORDKEY

  type 'a bst
  type 'a node = { left : 'a bst, key : Key.t, value : 'a, right : 'a bst }
  type key = Key.t

  val size : 'a bst -> int
  val empty : unit -> 'a bst
  val singleton : key * 'a -> 'a bst

  val makeNode : 'a node -> 'a bst
  val expose : 'a bst -> 'a node option
  val join : 'a bst * 'a bst -> 'a bst
  val splitAt : 'a bst * key -> 'a bst * 'a option * 'a bst

  val $ : key * 'a -> 'a bst
end
