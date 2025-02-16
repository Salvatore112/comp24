(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Common.StateMonad

let revert_cringe lst =
  let rec help lst = function
    | Ok acc ->
      (match lst with
       | x :: tl ->
         (match x with
          | Error _ as err -> err
          | Ok x -> help tl (Ok (x :: acc)))
       | [] -> Ok acc)
    | Error _ as err -> err
  in
  let res = help lst (Ok []) in
  match res with
  | Ok rev_lst -> Ok (List.rev rev_lst)
  | x -> x
;;

let middleend_transform_prog ast =
  match
    run (Alpha_conversion.alpha_convert_decl_list Alpha_conversion.init_context [] ast) 0
  with
  | _, Ok lst ->
    lst
    |> Closure_conversion.convert_ast
    |> Lambda_lifting.lift_ast
    |> fun x ->
    let list_of_res = Anf.transform x in
    revert_cringe list_of_res
  | _, Error x -> Error x
;;
