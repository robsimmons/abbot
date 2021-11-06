open! Base

module Map = Brother_tree.Map.Make (Int)

let%expect_test _ =
  let t = Map.of_list (List.init 10 ~f:(fun i -> (i, i))) in
  Core.print_s [%message "" ~_:(t : int Map.t)];
  [%expect{| ((0 0) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (7 7) (8 8) (9 9)) |}];
  let t = Map.add_exn t ~key:10 ~data:10 in
  Core.print_s [%message "" ~_:(t : int Map.t)];
  [%expect{| ((0 0) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (7 7) (8 8) (9 9) (10 10)) |}];
  let t = Map.add_exn t ~key:11 ~data:11 in
  Core.print_s [%message "" ~_:(t : int Map.t)];
  [%expect{| ((0 0) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (7 7) (8 8) (9 9) (10 10) (11 11)) |}];
  let t = Map.set t ~key:10 ~data:12 in
  Core.print_s [%message "" ~_:(t : int Map.t)];
  [%expect{| ((0 0) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (7 7) (8 8) (9 9) (10 12) (11 11)) |}];
  let t = Map.remove t 7 in
  Core.print_s [%message "" ~_:(t : int Map.t)];
  [%expect{| ((0 0) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (8 8) (9 9) (10 12) (11 11)) |}];
;;
