(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Anf
open Restore_src.RestoreSrc
open Typeinference
open Typeinference__StartState

let test_parse_and_convert_to_anf string_src =
  let res = Parser.parse_program string_src in
  match res with
  | Result.Ok prog ->
    Format.printf
      "%s"
      (restore_declarations (convert_declarations (Anf.anf_of_declarations prog)))
  | Result.Error e -> Format.printf "Parser error: %s" e
;;

let parse_and_convert_to_anf string_src =
  let res = Parser.parse_program string_src in
  match res with
  | Result.Ok prog ->
    restore_declarations (convert_declarations (Anf.anf_of_declarations prog))
  | Result.Error e -> e
;;

(* Expected anf programs *)

let%expect_test _ =
  test_parse_and_convert_to_anf
    {|
    let x = 5|};
  [%expect {| let  x = 5;; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf
    {|
    let x = 5 + 6|};
  [%expect
    {| let  x = (let  anf_var1 = (( + ) 5) in (let  anf_var2 = (anf_var1 6) in anf_var2));; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf
    {|
    let x = 7 + 8 + 9|};
  [%expect
    {| let  x = (let  anf_var1 = (( + ) 7) in (let  anf_var2 = (anf_var1 8) in (let  anf_var3 = (( + ) anf_var2) in (let  anf_var4 = (anf_var3 9) in anf_var4))));; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf
    {|
    let rec fac = fun n -> if n = 0 then 1 else n * (fac (n - 1))|};
  [%expect
    {|
    let rec fac = (fun n -> (let  anf_var1 = (( = ) n) in (let  anf_var2 = (anf_var1 0) in (if (anf_var2) then 1 else ((let  anf_var3 = (( * ) n) in (let  anf_var4 = (( - ) n) in (let  anf_var5 = (anf_var4 1) in (let  anf_var6 = (fac anf_var5) in (let  anf_var7 = (anf_var3 anf_var6) in anf_var7))))))))));; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf
    {|
    let fibo = fun n -> let rec fiboCPS = fun n acc -> match n with
     | 0 -> acc 0
     | 1 -> acc 1
     | _ -> fiboCPS (n - 1) (fun x -> fiboCPS (n - 2) (fun y -> acc (x + y)))
     in
       fiboCPS n (fun x -> x)
      |};
  [%expect
    {|
    let  fibo = (fun n -> (let rec fiboCPS = (fun n -> (fun acc -> (match n with
    | 0 -> (let  anf_var1 = (acc 0) in anf_var1)
    | 1 -> (let  anf_var1 = (acc 1) in anf_var1)
    | _ -> (let  anf_var1 = (( - ) n) in (let  anf_var2 = (anf_var1 1) in (let  anf_var3 = (fiboCPS anf_var2) in (let  anf_var5 = (anf_var3 (fun x -> (let  anf_var1 = (( - ) n) in (let  anf_var2 = (anf_var1 2) in (let  anf_var3 = (fiboCPS anf_var2) in (let  anf_var4 = (anf_var3 (fun y -> (let  anf_var1 = (( + ) x) in (let  anf_var2 = (anf_var1 y) in (let  anf_var3 = (acc anf_var2) in anf_var3))))) in anf_var4)))))) in anf_var5))))))) in (let  anf_var6 = (fiboCPS n) in (let  anf_var1 = (anf_var6 (fun x -> x)) in anf_var1))));; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf {|let x = (5 + 6 + 7, 21 + 3, 30)|};
  [%expect
    {|
    let  x = (let  anf_var2 = (( + ) 5) in (let  anf_var3 = (anf_var2 6) in (let  anf_var4 = (( + ) anf_var3) in (let  anf_var5 = (anf_var4 7) in (let  anf_var7 = (( + ) 21) in (let  anf_var8 = (anf_var7 3) in ((let  anf_var1 = anf_var5 in anf_var1), (let  anf_var6 = anf_var8 in anf_var6), (let  anf_var9 = 30 in anf_var9))))))));; |}]
;;

let%expect_test _ =
  test_parse_and_convert_to_anf {|let (x : int -> int) = 5 + 6 + 7|};
  [%expect
    {| let  (x : (int -> int)) = (let  anf_var1 = (( + ) 5) in (let  anf_var2 = (anf_var1 6) in (let  anf_var3 = (( + ) anf_var2) in (let  anf_var4 = (anf_var3 7) in anf_var4))));; |}]
;;

(* Anf program should have the same type tests *)

let%test _ =
  let test_program = {|let  x = 5;;|} in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;

let%test _ =
  let test_program = {|let x = 5 + 6;;|} in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;

let%test _ =
  let test_program = {|let x = 7 + 8 + 9;;|} in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;

let%test _ =
  let test_program =
    {|
    let fibo = fun n -> let rec fiboCPS = fun n acc -> match n with
     | 0 -> acc 0
     | 1 -> acc 1
     | _ -> fiboCPS (n - 1) (fun x -> fiboCPS (n - 2) (fun y -> acc (x + y)))
     in
       fiboCPS n (fun x -> x)
      |}
  in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;

let%test _ =
  let test_program = {|let x = (5 + 6 + 7, 21 + 3, 30);;|} in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;

let%test _ =
  let test_program = {|let (x : int) = 5 + 6 + 7;;|} in
  test_infer_prog start_state test_program
  = test_infer_prog start_state (parse_and_convert_to_anf test_program)
;;
