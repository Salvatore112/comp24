(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Common.StateMonad
open Ast
open Pe_ast

type state = int

let read_counter =
  let* cnt = read in
  return cnt
;;

let write_counter cnt = write cnt

let get_field target field_num =
  CApplication
    ( CApplication (CImmExpr (Middleend.Anf_ast.ImmIdentifier "get_box_field"), target)
    , CImmExpr (Middleend.Anf_ast.ImmInt field_num) )
;;

let check_box_tag target tag =
  CApplication
    ( CApplication (CImmExpr (Middleend.Anf_ast.ImmIdentifier "check_box_tag"), target)
    , CImmExpr (Middleend.Anf_ast.ImmInt tag) )
;;

let const_to_imm = function
  | CBool b -> Middleend.Anf_ast.ImmBool b
  | CInt i -> Middleend.Anf_ast.ImmInt i
  | CUnit -> Middleend.Anf_ast.ImmUnit
  | CNil -> Middleend.Anf_ast.ImmNil
;;

let compair_expr_cnst cexp cnst =
  CApplication
    ( CApplication (CImmExpr (Middleend.Anf_ast.ImmIdentifier "( = )"), cexp)
    , CImmExpr (const_to_imm cnst) )
;;

let result_match res =
  CImmExpr (Middleend.Anf_ast.ImmTuple [ Middleend.Anf_ast.ImmInt 1; res ])
;;

let fail_match =
  CImmExpr
    (Middleend.Anf_ast.ImmTuple [ Middleend.Anf_ast.ImmInt 0; Middleend.Anf_ast.ImmInt 0 ])
;;

let fresh_var name =
  let* cnt = read_counter in
  return (Format.sprintf "%s_%d_pe" name cnt)
;;

let cexpr_from_name name = CImmExpr (Middleend.Anf_ast.ImmIdentifier name)

let result_match_cexpr exp =
  let* res = fresh_var "res" in
  return (ALetIn (res, exp, ACExpr (result_match (Middleend.Anf_ast.ImmIdentifier res))))
;;

let rec eliminate_pattern_match : pattern -> cexpr -> aexpr -> (state, aexpr) t =
  fun pat target_exp cont ->
  (*
     RESULT CODE:

     let <var_name> = check_tag(target_exp, <tag>)
     if <var_name>
     --then
     ----<cont_block>
     --else
     ----(0, 0)
  *)
  let create_final_tag_check_box var_name tag cont_block =
    let* check_var = fresh_var var_name in
    let fin_block_in =
      ACExpr
        (CIfThenElse
           (Middleend.Anf_ast.ImmIdentifier check_var, cont_block, ACExpr fail_match))
    in
    return (ALetIn (check_var, check_box_tag target_exp tag, fin_block_in))
  in
  (*
     RESULT CODE:

     let <var_name> = get_field(target, <field_num>) in
     -- [sub_pat elimination]
     ----<cont_block>
  *)
  let create_sub_pattern_elim_block var_name field_num sub_pat cont_block =
    let* field_var = fresh_var var_name in
    let* sub_pat_elim =
      eliminate_pattern_match sub_pat (cexpr_from_name field_var) cont_block
    in
    return (ALetIn (field_var, get_field target_exp field_num, sub_pat_elim))
  in
  match pat with
  | PConstraint (pat, _) -> eliminate_pattern_match pat target_exp cont
  | PWildCard -> return cont
  | PIdentifier id_name -> return (ALetIn (id_name, target_exp, cont))
  | PConstant const ->
    let* const_check = fresh_var "const_check" in
    let if_block =
      CIfThenElse (Middleend.Anf_ast.ImmIdentifier const_check, cont, ACExpr fail_match)
    in
    return (ALetIn (const_check, compair_expr_cnst target_exp const, ACExpr if_block))
  | PCons (head_pat, tail_pat) ->
    (*
       RESULT CODE:

       let cons_check = check_tag(target, 0)
       if cons_check
       --then
       ----let cons_head = get_field(target, 0) in
       ----<head pattern elim>
       -------let tail_cons = get_field(target, 1) in
       -------<tail pattern elim>
       ---------<cont>
       --else
       ----(0, 0)
    *)
    let* tail_block = create_sub_pattern_elim_block "tail_cons" 1 tail_pat cont in
    let* head_block = create_sub_pattern_elim_block "head_cons" 0 head_pat tail_block in
    create_final_tag_check_box "cons_check" 0 head_block
  | PTuple lst_pat ->
    let* _, fin_block =
      List.fold_left
        (fun res pat ->
          let* i, fin_block = res in
          let* new_block = create_sub_pattern_elim_block "tuple_elem" i pat fin_block in
          return (i + 1, new_block))
        (return (0, cont))
        lst_pat
    in
    create_final_tag_check_box "tuple_check" 0 fin_block
;;

(** Will return "code" like
    ```
    let temp_res = if <pattern_mathing code with rt functions>
    then let res = <choosed aexpr>
    (1, res)
    else (0, 0)
    let match_complete = rt.get_field(temp_res, 0) in
    let res = rt.get_field(temp_res, 1) in
    <continuation call code>
    ``` *)
(* let eliminate_pat_with_res: aexpr -> pattern -> (state, cexpr) t *)

let rec eliminate_cexpr : Middleend.Anf_ast.cexpr -> (state, cexpr) t = function
  | CImmExpr imm -> return (CImmExpr imm)
  | CApplication (cexp1, cexp2) ->
    let* pe_cexp1 = eliminate_cexpr cexp1 in
    let* pe_cexp2 = eliminate_cexpr cexp2 in
    return (CApplication (pe_cexp1, pe_cexp2))
  (* | CMatch (imm, pat_aexp_list) -> fail "boba" *)
  | _ -> fail "das"
;;
