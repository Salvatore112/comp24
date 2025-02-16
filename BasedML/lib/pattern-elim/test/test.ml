(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Pe_to_str

let test_infer_prog string_exp =
  let res = Parser.parse_program string_exp in
  match res with
  | Result.Ok prog ->
    let res = Typeinference.infer_prog prog in
    (match res with
     | Result.Ok _ ->
       let anf_res = Middleend.Full.middleend_transform_prog prog in
       (match anf_res with
        | Ok anf_ast ->
          let pe_res = Pattern_elim.Elimination.eliminate_from_prog anf_ast in
          (match pe_res with
           | Ok pe_ast ->
             Format.printf
               "ANF: \n%s\n\n\nPE: \n%a"
               (Middleend.Anf_to_str.program_to_string anf_ast)
               prog_to_str
               pe_ast
           | Error s -> Format.printf "Pattern elimination error: %s" s)
        | Error s -> Format.printf "Middleend error: %s" s)
     | Result.Error s -> Format.printf "Infer error: %s" s)
  | Result.Error e -> Format.printf "Parser error: %s" e
;;

let%expect_test "Late binding var" =
  test_infer_prog {|
let (a, b) = (2, 3)
|};
  [%expect
    {|
    ANF:
    let  (a_0, b_0) = let anf_tuple_0 = (2, 3) in
    anf_tuple_0;;


    PE:
    let  global_res_pe = (let match_comp_6_pe = (((get_box_field) (let tuple_check_5_pe = (((check_box_tag) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (0)) in (if tuple_check_5_pe then (let tuple_elem_4_pe = (((get_box_field) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (1)) in (let b_0_inner_pe = (tuple_elem_4_pe) in (let tuple_elem_3_pe = (((get_box_field) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (0)) in (let a_0_inner_pe = (tuple_elem_3_pe) in (let res_2_pe = ((b_0_inner_pe, a_0_inner_pe)) in ((true, res_2_pe))))))) else ((false, 0))))) (0)) in (if match_comp_6_pe then (((get_box_field) (let tuple_check_5_pe = (((check_box_tag) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (0)) in (if tuple_check_5_pe then (let tuple_elem_4_pe = (((get_box_field) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (1)) in (let b_0_inner_pe = (tuple_elem_4_pe) in (let tuple_elem_3_pe = (((get_box_field) (let match_comp_1_pe = (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (0)) in (if match_comp_1_pe then (((get_box_field) (let anf_tuple_0 = ((2, 3)) in (let res_0_pe = (anf_tuple_0) in ((true, res_0_pe))))) (1)) else ((match_failure) ([]))))) (0)) in (let a_0_inner_pe = (tuple_elem_3_pe) in (let res_2_pe = ((b_0_inner_pe, a_0_inner_pe)) in ((true, res_2_pe))))))) else ((false, 0))))) (1)) else ((match_failure) ([]))));;
    let  b_0 = (((get_box_field) (global_res_pe)) (0));;
    let  a_0 = (((get_box_field) (global_res_pe)) (1));;
    |}]
;;
