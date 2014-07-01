signature TABLE =
sig
  structure Key : EQKEY
  structure Seq : SEQUENCE
  structure Set : SET where Key = Key and Seq = Seq

  type 'a table
  type 'a seq = 'a Seq.seq
  type key = Key.t
  type set = Set.t

  val size : 'a table -> int
  val domain : 'a table -> set
  val range : 'a table -> 'a seq
  val toString : ('a -> string) -> 'a table -> string
  val toSeq : 'a table -> (key * 'a) seq

  val find : 'a table -> key -> 'a option
  val insert : ('a * 'a -> 'a) -> (key * 'a) -> 'a table -> 'a table
  val delete : key -> 'a table -> 'a table

  val empty : unit -> 'a table
  val singleton : key * 'a -> 'a table
  val tabulate : (key -> 'a) -> set -> 'a table
  val collect : (key * 'a) seq -> 'a seq table
  val fromSeq : (key * 'a) seq -> 'a table

  val map     : ('a -> 'b) -> 'a table -> 'b table
  val mapk    : (key * 'a -> 'b) -> 'a table -> 'b table
  val filter  : ('a -> bool) -> 'a table -> 'a table
  val filterk : (key * 'a -> bool) -> 'a table -> 'a table

  val iter   : ('b * (key * 'a) -> 'b) -> 'b -> 'a table -> 'b
  val iterh  : ('b * (key * 'a) -> 'b) -> 'b -> 'a table -> ('b table * 'b)
  val reduce : ('a * 'a -> 'a) -> 'a -> 'a table -> 'a

  val merge   : ('a * 'a -> 'a) -> ('a table * 'a table) -> 'a table
  val extract : 'a table * set -> 'a table
  val erase   : 'a table * set -> 'a table

  val $ : (key * 'a) -> 'a table
end
