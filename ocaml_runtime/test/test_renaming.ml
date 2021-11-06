(* CR wduff: Re-enable these tests.

   {[
     open! Base
     open Abbot_runtime

     let show_raise f =
       match f () with
       | () -> print_s [%message "did not raise."]
       | exception exn ->
         print_s [%message "raised exception" (exn : exn)]
     ;;

     let%expect_test "bind" =
       let test to_bind bind_in =
         let result = Renaming.apply (Renaming.bind to_bind) bind_in in
         print_s [%message "" (to_bind : Temp.t) (bind_in : Internal_var.t) (result : Internal_var.t)]
       in
       let x = Temp.create "x" in
       let y = Temp.create "y" in
       test x (Free_var x);
       [%expect{| ((to_bind (x 1)) (bind_in (Free_var (x 1))) (result (Bound_var 0))) |}];
       test x (Free_var y);
       [%expect{| ((to_bind (x 1)) (bind_in (Free_var (y 2))) (result (Free_var (y 2)))) |}];
       test x (Bound_var 0);
       [%expect{| ((to_bind (x 1)) (bind_in (Bound_var 0)) (result (Bound_var 1))) |}];
       test x (Bound_var 1);
       [%expect{| ((to_bind (x 1)) (bind_in (Bound_var 1)) (result (Bound_var 2))) |}]
     ;;

     let%expect_test "unbind" =
       let test to_unbind unbind_in =
         let result = Renaming.apply (Renaming.unbind to_unbind) unbind_in in
         print_s
           [%message "" (to_unbind : Temp.t) (unbind_in : Internal_var.t) (result : Internal_var.t)]
       in
       let x = Temp.create "x" in
       let y = Temp.create "y" in
       show_raise (fun () -> test x (Free_var x));
       [%expect{|
    ("raised exception"
     (exn
      ("Internal abbot bug. Variable passed to [unbind] was not fresh."
       (var (x 3))))) |}];
       test x (Free_var y);
       [%expect{| ((to_unbind (x 3)) (unbind_in (Free_var (y 4))) (result (Free_var (y 4)))) |}];
       test x (Bound_var 0);
       [%expect{| ((to_unbind (x 3)) (unbind_in (Bound_var 0)) (result (Free_var (x 3)))) |}];
       test x (Bound_var 1);
       [%expect{| ((to_unbind (x 3)) (unbind_in (Bound_var 1)) (result (Bound_var 0))) |}]
     ;;

     let%expect_test "unbind o bind" =
       let test var in_ =
         let result = Renaming.apply (Renaming.compose (Renaming.unbind var) (Renaming.bind var)) in_ in
         match Internal_var.equal in_ result with
         | true -> ()
         | false ->
           raise_s
             [%message
               "Did not round trip"
                 (var : Temp.t)
                 (in_ : Internal_var.t)
                 (result : Internal_var.t)]
       in
       let x = Temp.create "x" in
       let y = Temp.create "y" in
       test x (Free_var x);
       [%expect{||}];
       test x (Free_var y);
       [%expect{||}];
       test x (Bound_var 0);
       [%expect{||}];
       test x (Bound_var 1);
       [%expect{||}]
     ;;

     let%expect_test "bind o unbind" =
       let test var in_ =
         let result = Renaming.apply (Renaming.compose (Renaming.bind var) (Renaming.unbind var)) in_ in
         match Internal_var.equal in_ result with
         | true -> ()
         | false ->
           raise_s
             [%message
               "Did not round trip"
                 (var : Temp.t)
                 (in_ : Internal_var.t)
                 (result : Internal_var.t)]
       in
       let x = Temp.create "x" in
       let y = Temp.create "y" in
       show_raise (fun () -> test x (Free_var x));
       [%expect{|
    ("raised exception"
     (exn
      ("Did not round trip" (var (x 7)) (in_ (Free_var (x 7)))
       (result (Bound_var 0))))) |}];
       test x (Free_var y);
       [%expect{||}];
       test x (Bound_var 0);
       [%expect{||}];
       test x (Bound_var 1);
       [%expect{||}]
     ;;
   ]}
*)
