structure Random210 : RANDOM210 =
struct
  structure Seq = ArraySequence

  type rand = Word.word

  val magicNext = 0wx50356BCB
  val magicSplit = 0wx3A9DB073
  val magicStringHash = 0w65599

  fun next r = Word.*(magicNext, (r + 0w1))

  fun fromInt i = next(Word.fromInt i)

  fun split r = (next r, next(Word.+(r, magicSplit)))

  fun randomInt r NONE i =
        Word.toIntX(next(Word.+(Word.fromInt i, r)))
      | randomInt r (SOME (low, high)) i =
        ((randomInt r NONE i) mod (high - low)) + low

  fun randomReal r NONE i =
      let val maxInt = valOf Int.maxInt
      in Real.fromInt (Int.abs (randomInt r NONE i)) / Real.fromInt maxInt
      end
    | randomReal r (SOME (low, high)) i =
      low + (randomReal r NONE i) * (high - low)

  fun randomIntSeq r range len = Seq.tabulate (randomInt r range) len

  fun randomRealSeq r range len = Seq.tabulate (randomReal r range) len

  fun hashInt r i = randomInt r NONE i

  fun hashString r str =
      let fun subs i = Word.fromInt (Char.ord (String.sub(str, i)))
          fun hash(i, h) = if (i < 0) then h
                           else hash (i - 1, (subs i) + h*magicStringHash)
      in Word.toIntX (hash ((String.size str) - 1, r))
      end

  local
    structure R = Random
    open Seq
  in
  (* note that this is sequential to ensure thread safety. it's fast *)
  fun flip (seed : rand) (length : int) : int seq =
      let
        val r = R.rand (Word.toIntX seed, Word.toIntX(0wx2c0ffee))
        val yield = fn () => R.randRange (0,1) r
        val yield_wrapper = fn (_, _) => yield ()
        val (s, _) = iterh yield_wrapper (yield ())
                           (tabulate (fn _ => ()) length)
      in
        s
      end
  end


end
