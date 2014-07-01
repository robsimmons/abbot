signature RANDOM210 =
sig
  structure Seq : SEQUENCE

  type rand

  val fromInt : int -> rand
  val next: rand -> rand
  val split : rand -> (rand * rand)

  val randomInt: rand -> ((int * int) option) -> int -> int
  val randomReal : rand -> ((real * real) option)-> int -> real

  val randomIntSeq: rand -> ((int * int) option) -> int -> int Seq.seq
  val randomRealSeq: rand -> ((real * real) option) -> int -> real Seq.seq

  val hashInt : rand -> int -> int
  val hashString : rand -> string -> int
  val flip: rand -> int -> int Seq.seq
  end
