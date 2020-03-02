structure External_abts = struct
functor Make0 (T : sig type t end) :> EXTERNAL_ABT_0 where type t = T.t = struct
type t = T.t

fun apply_renaming _ acc t = (acc, t)
fun subst _ t = t
end

functor Make1
            (T : sig
                 type 'a t

                 val fold_map
                     :  'a t
                        -> 'acc
                        -> ('acc -> 'a -> 'acc * 'b)
                        -> 'acc * 'b t
             end)
        :> EXTERNAL_ABT_1 where type 'a t = 'a T.t =
struct
type 'a t = 'a T.t

fun apply_renaming apply_renaming_a renaming acc t =
    T.fold_map t acc (apply_renaming_a renaming)

fun subst subst_a sub t =
    let val ((), t) =
            T.fold_map
                t
                ()
                (fn () => fn a => ((), subst_a sub a))
    in
        t
    end
end

structure Unit = Make0 (struct type t = unit end)

structure Int = Make0 (struct type t = int end)


structure Char = Make0 (struct type t = char end)

structure String = Make0 (struct type t = string end)

structure Option =
Make1 (struct
        type 'a t = 'a option

        fun fold_map t init f =
            case t
             of NONE => (init, NONE)
              | SOME data =>
                let val (acc, data) = f init data in
                    (acc, SOME data)
                end
        end)

structure List =
Make1 (struct
        type 'a t = 'a list

        fun fold_map t init f =
            let val (acc, rev_list) =
                    List.foldl
                        (fn (elt, (acc, rev_list)) =>
                            let val (acc, elt) = f acc elt in
                                (acc, elt :: rev_list)
                            end)
                        (init, [])
                        t
            in
                (acc, List.rev rev_list)
            end
        end)
end
