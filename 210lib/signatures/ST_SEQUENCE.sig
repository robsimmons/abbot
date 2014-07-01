signature ST_SEQUENCE =
sig
  structure Seq : SEQUENCE

  type 'a stseq

  exception Range

  val fromSeq : 'a Seq.seq -> 'a stseq
  val toSeq : 'a stseq -> 'a Seq.seq
  val nth : 'a stseq -> int -> 'a

  val update : (int * 'a) -> 'a stseq -> 'a stseq
  val inject : (int * 'a) Seq.seq -> 'a stseq -> 'a stseq
end
