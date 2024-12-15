(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Anf_ast
open Ast
open Restore_src.RestoreSrc

(* references https://www.cs.swarthmore.edu/~jpolitz/cs75/s16/n_anf-tutorial.html *)
(* Generate anf variables *)
let test_restore_src tree = Format.printf "%s" (restore_declarations tree)
let counter = ref 0
let set n = counter := n

let new_var () =
  incr counter;
  Format.sprintf "anf_var%d" !counter
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
      let rec create_tuple acc = function
        | [] -> expr_with_hole (ImmediateTuple (List.rev acc))
        | h :: tl ->
          let new_name = new_var () in
          helper h (fun imm ->
            let let_binding =
              ANFLetIn
                ( NotRec
                , PIdentifier new_name
                , CImmExpr imm
                , expr_with_hole (ImmediateIdentifier new_name) )
            in
            create_tuple (let_binding :: acc) tl)
      in
      create_tuple [] exps
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

let rec convert_aexpr (ae : aexpr) : expr =
  match ae with
  | ANFCEexpr cexpr -> convert_cexpr cexpr
  | ANFLetIn (rec_flag, pattern, cexpr, body) ->
    let rhs = convert_cexpr cexpr in
    let body' = convert_aexpr body in
    ELetIn (rec_flag, pattern, rhs, body')
  | ANFIfThenElse (cond, then_expr, else_expr) ->
    EIfThenElse (convert_aexpr cond, convert_aexpr then_expr, convert_aexpr else_expr)
  | ANFTuple exprs -> ETuple (List.map convert_aexpr exprs)
  | ANFMatch (pat, branches) ->
    let branches' = List.map (fun (p, e) -> p, convert_aexpr e) branches in
    EMatch (pat, branches')
  | ANFConstraint (e, t) -> EConstraint (convert_aexpr e, t)

and convert_cexpr (ce : cexpr) : expr =
  match ce with
  | CImmExpr imm -> convert_immexpr imm
  | CApp (imm1, imm2) -> EApplication (convert_immexpr imm1, convert_immexpr imm2)

and convert_immexpr (imm : immexpr) : expr =
  match imm with
  | ImmediateInt i -> EConstant (CInt i)
  | ImmediateBool b -> EConstant (CBool b)
  | ImmediateUnit -> EConstant CUnit
  | ImmediateNil -> EConstant CNil
  | ImmediateIdentifier id -> EIdentifier id
  | ImmediateTuple aexprs -> ETuple (List.map convert_aexpr aexprs)
  | ImmediateFunc (pattern, body) -> EFunction (pattern, convert_aexpr body)
;;

let rec convert_let_declaration (let_decl : anf_let_declaration) : let_declaration =
  match let_decl with
  | ANFSingleLet (rec_flag, anf_single_let) ->
    DSingleLet (rec_flag, convert_let_single anf_single_let)
  | ANFMutualRecDecl (rec_flag, anf_single_lets) ->
    DMutualRecDecl (rec_flag, List.map convert_let_single anf_single_lets)

and convert_let_single (anf_single_let : anf_single_let) : single_let =
  match anf_single_let with
  | ANFDec (pattern, aexpr) -> DLet (pattern, convert_aexpr aexpr)
;;

(* Convert the list of ANF declarations to regular declarations *)
let convert_declarations (anf_decls : anf_declarations) : declarations =
  List.map convert_let_declaration anf_decls
;;

let test_ast decls = Format.print_string (show_declarations (convert_declarations decls))
