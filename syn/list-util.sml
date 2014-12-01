structure List_Util =
struct
  fun mem equal x xs = List.exists (fn y => equal(x, y)) xs
  fun remove equal x xs = List.filter (fn y => not (equal(x,y))) xs

  fun zip_exact e [] [] = []
    | zip_exact e (x :: xs) (y :: ys) = (x,y) :: (zip_exact e xs ys)
    | zip_exact e _ _ = raise e

  (* Quadratic(!) algorithm to make a list without duplicates *)
  fun collate equal xss =
      let fun loop acc [] = acc
            | loop acc ([] :: yss) = loop acc yss
            | loop acc ((y :: ys) :: yss) =
              if mem equal y acc then
                loop acc (ys :: yss)
              else
                loop (y :: acc) (ys :: yss)
      in loop [] xss end

  (* Determines whether all elements of a list are equivalent to each other *)
  fun allequiv equiv [] = NONE
    | allequiv equiv (x::xs) =
      if List.all (fn y => equiv x y) xs
      then SOME x
      else NONE

  fun zipTest p [] [] = true
    | zipTest p (x :: xs) (y :: ys) = p(x, y) andalso zipTest p xs ys
    | zipTest p _ _  = false

  fun isSet eq l =
      case l of
          [] => true
        | x::xs =>
          (not (List.exists (fn z => eq (x, z)) xs))
          andalso isSet eq xs
end
