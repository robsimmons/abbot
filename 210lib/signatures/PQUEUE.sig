signature PQUEUE =
sig
  structure Key : ORDKEY

  type 'a pq
  type key = Key.t

  val empty : unit -> 'a pq
  val singleton : (key * 'a) -> 'a pq
  val fromList : (key * 'a) list -> 'a pq

  val size : 'a pq -> int
  val findMin : 'a pq -> (key * 'a) option

  val insert : (key * 'a) -> 'a pq -> 'a pq
  val deleteMin : 'a pq -> (key * 'a) option * 'a pq
  val meld : ('a pq * 'a pq) -> 'a pq

  type 'a t = 'a pq
  val $ : (key * 'a) -> 'a pq
  val % : (key * 'a) list -> 'a pq
end
