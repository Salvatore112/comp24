(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Anf_ast
open Ast

(* references https://www.cs.swarthmore.edu/~jpolitz/cs75/s16/n_anf-tutorial.html *)
(* Generate anf variables *)
let counter = ref 0
let set n = counter := n

let new_var () =
  incr counter;
  Format.sprintf "$ANF_VAR$%d" !counter
;;

let rec anf_of_exp e expr_with_hole =
  let immediate_of_const = function
    | CInt i -> ImmediateInt i
    | CBool b -> ImmediateBool b
    | CNil -> ImmediateNil
    | CUnit -> ImmediateUnit
  in
  set 0;
  let rec helper e expr_with_hole =
    match e with
    | EIdentifier str -> expr_with_hole (ImmediateIdentifier str)
    | EConstant value -> expr_with_hole (immediate_of_const value)
    | EConstraint (exp, typ) ->
      helper exp (fun imm -> ANFConstraint (expr_with_hole imm, typ))
    | EMatch (pat, cases) ->
      let rec convert_cases cases acc =
        match cases with
        | (pat, exp) :: tl ->
          let anf_exp = anf_of_exp exp (fun immexpr -> expr_with_hole immexpr) in
          convert_cases tl ((pat, anf_exp) :: acc)
        | [] -> List.rev acc
      in
      ANFMatch (pat, convert_cases cases [])
    | ETuple exps ->
      (* Convert each expression in the tuple individually, then gather them into a tuple *)
      let rec create_tuple_list acc = function
        | [] -> List.rev acc
        | h :: tl ->
          let anf_body = anf_of_exp h (fun imm -> ANFCEexpr (CImmExpr imm)) in
          create_tuple_list (anf_body :: acc) tl
      in
      expr_with_hole (ImmediateTuple (create_tuple_list [] exps))
    | EApplication (left, right) ->
      helper left (fun left_immediate ->
        helper right (fun right_immediate ->
          let new_name = new_var () in
          ANFLetIn
            ( NotRec
            , PIdentifier new_name
            , CApp (left_immediate, right_immediate)
            , expr_with_hole (ImmediateIdentifier new_name) )))
    | ELetIn (flag, str, exp1, exp2) ->
      helper exp1 (fun exp1_immediate ->
        ANFLetIn (flag, str, CImmExpr exp1_immediate, helper exp2 expr_with_hole))
    | EIfThenElse (guard, if_body, else_body) ->
      helper guard (fun guard_immediate ->
        ANFIfThenElse
          ( expr_with_hole guard_immediate
          , helper if_body (fun if_body_immediate -> expr_with_hole if_body_immediate)
          , helper else_body (fun else_body_immediate ->
              expr_with_hole else_body_immediate) ))
    | EFunction (pat, body) ->
      (* Convert the body of the function into ANF *)
      let anf_body = anf_of_exp body (fun imm -> ANFCEexpr (CImmExpr imm)) in
      expr_with_hole (ImmediateFunc (pat, anf_body))
  in
  helper e expr_with_hole
;;

let anf_of_declaration decl =
  match decl with
  | DSingleLet (flag, DLet (pat, expr)) ->
    let converted_expr = anf_of_exp expr (fun imm -> ANFCEexpr (CImmExpr imm)) in
    ANFSingleLet (flag, ANFDec (pat, converted_expr))
  | DMutualRecDecl (flag, bindings) ->
    let convert_binding (DLet (pat, expr)) =
      let converted_expr = anf_of_exp expr (fun imm -> ANFCEexpr (CImmExpr imm)) in
      ANFDec (pat, converted_expr)
    in
    let converted_bindings = List.map convert_binding bindings in
    ANFMutualRecDecl (flag, converted_bindings)
;;

let anf_of_declarations decls = List.map anf_of_declaration decls

let test_prog decls =
  Format.print_string (show_anf_declarations (anf_of_declarations decls))
;;
