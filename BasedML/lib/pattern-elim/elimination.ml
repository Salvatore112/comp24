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

let pe_suffix = "_pe"

let fresh_var name =
  let* cnt = read_counter in
  return (Format.sprintf "%s_%d%s" name cnt pe_suffix)
;;

let cexpr_from_name name = CImmExpr (Middleend.Anf_ast.ImmIdentifier name)

let result_match_aexpr exp =
  let* res = fresh_var "res" in
  return (ALetIn (res, exp, result_match (Middleend.Anf_ast.ImmIdentifier res)))
;;

let rec eliminate_pattern_match : pattern -> pe_expr -> pe_expr -> (state, pe_expr) t =
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
      CIfThenElse (Middleend.Anf_ast.ImmIdentifier check_var, cont_block, fail_match)
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
      CIfThenElse (Middleend.Anf_ast.ImmIdentifier const_check, cont, fail_match)
    in
    return (ALetIn (const_check, compair_expr_cnst target_exp const, if_block))
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

let match_error =
  CApplication
    ( CImmExpr (Middleend.Anf_ast.ImmIdentifier "match_failure")
    , CImmExpr Middleend.Anf_ast.ImmNil )
;;

let if_match_block combined_res on_succ_block on_fail_block =
  let* match_complete = fresh_var "match_comp" in
  let if_block =
    CIfThenElse
      (Middleend.Anf_ast.ImmIdentifier match_complete, on_succ_block, on_fail_block)
  in
  let get_block = ALetIn (match_complete, get_field combined_res 0, if_block) in
  return get_block
;;

let if_match_fail_block combined_res on_fail_block =
  if_match_block combined_res (get_field combined_res 1) on_fail_block
;;

let rec eliminate_from_cexpr : Middleend.Anf_ast.cexpr -> (state, pe_expr) t = function
  | CImmExpr imm -> return (CImmExpr imm)
  | CApplication (cexp1, cexp2) ->
    let* pe_cexp1 = eliminate_from_cexpr cexp1 in
    let* pe_cexp2 = eliminate_from_cexpr cexp2 in
    return (CApplication (pe_cexp1, pe_cexp2))
  | CIfThenElse (imm, aexp1, aexp2) ->
    let* pe_aexp1 = eliminate_from_aexpr aexp1 in
    let* pe_aexp2 = eliminate_from_aexpr aexp2 in
    return (CIfThenElse (imm, pe_aexp1, pe_aexp2))
  | CMatch (imm, pat_aexp_list) ->
    let target_exp = CImmExpr imm in
    let help_fun pat res_exp prev_res cont =
      let* combined_res = fresh_var "combined_res" in
      let* math_res_block = result_match_aexpr res_exp in
      let* pe_block = eliminate_pattern_match pat target_exp math_res_block in
      let* cont_block = cont (Some combined_res) in
      let new_match = ALetIn (combined_res, pe_block, cont_block) in
      match prev_res with
      | Some prev_res -> if_match_fail_block (cexpr_from_name prev_res) new_match
      | None -> return new_match
    in
    let fail_block = function
      | Some match_res -> if_match_fail_block (cexpr_from_name match_res) match_error
      | None -> fail "Imposible error: match without pattern matchin?"
    in
    let final_block =
      (List.fold_right
         (fun (pat, anf_aexp) cont prev_res ->
           let* pe_aexp = eliminate_from_aexpr anf_aexp in
           help_fun pat pe_aexp prev_res cont)
         pat_aexp_list
         fail_block)
        None
    in
    final_block

and eliminate_from_aexpr : Middleend.Anf_ast.aexpr -> (state, pe_expr) t = function
  | ACExpr cexp ->
    let* pe_cexp = eliminate_from_cexpr cexp in
    return pe_cexp
  | ALetIn (pat, cexp, aexp) ->
    let* pe_cexp = eliminate_from_cexpr cexp in
    let* pe_aexp = eliminate_from_aexpr aexp in
    let* match_res_block = result_match_aexpr pe_aexp in
    let* pe_block = eliminate_pattern_match pat pe_cexp match_res_block in
    if_match_fail_block pe_block match_error
;;
