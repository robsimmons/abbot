open! Base

module Map = Core.Map

val choose_key : ('k, 'v, 'cmp) Map.t -> 'k option

val remove_set : ('k, 'v, 'cmp) Map.t -> ('k, 'cmp) Set.t -> ('k, 'v, 'cmp) Map.t
val restrict_to_set : ('k, 'v, 'cmp) Map.t -> ('k, 'cmp) Set.t -> ('k, 'v, 'cmp) Map.t

val union
  :  ('k, 'v, 'cmp) Map.t
  -> ('k, 'v, 'cmp) Map.t
  -> merge:(key:'k -> 'v -> 'v -> 'v)
  -> ('k, 'v, 'cmp) Map.t

val inter
  :  ('k, 'a, 'cmp) Map.t
  -> ('k, 'b, 'cmp) Map.t
  -> merge:(key:'k -> 'a -> 'b -> 'c)
  -> ('k, 'c, 'cmp) Map.t

val symm_diff
  :  ('k, 'a, 'cmp) Map.t
  -> ('k, 'a, 'cmp) Map.t
  -> ('k, 'a, 'cmp) Map.t
