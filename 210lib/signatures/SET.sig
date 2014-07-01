signature SET =
sig
  structure Key : EQKEY
  structure Seq : SEQUENCE

  type set
  type key = Key.t

  val size : set -> int
  val toString : set -> string
  val toSeq : set -> key Seq.seq

  val empty : unit -> set
  val singleton : key -> set
  val fromSeq : key Seq.seq -> set

  val find : set -> key -> bool
  val insert : key -> set -> set
  val delete : key -> set -> set

  val filter : (key -> bool) -> set -> set

  val union : set * set -> set
  val intersection : set * set -> set
  val difference : set * set -> set

  type t = set
  val $ : key -> set
end
