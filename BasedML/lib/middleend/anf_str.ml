(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Ast
open Anf_ast

let rec pp_type_name tp =
  let rec_call tp = pp_type_name tp in
  match tp with
  | TUnit -> "unit"
  | TInt -> "int"
  | TBool -> "bool"
  | TPoly name -> "'" ^ name
  | TTuple lst -> "(" ^ String.concat " * " (List.map rec_call lst) ^ ")"
  | TFunction (tp_arg, tp_ret) ->
    "(" ^ pp_type_name tp_arg ^ " -> " ^ pp_type_name tp_ret ^ ")"
  | TList tp -> "(" ^ pp_type_name tp ^ " list)"
;;

let frestore_constant c =
  match c with
  | CInt i -> string_of_int i
  | CBool false -> "false"
  | CBool true -> "true"
  | CNil -> "[]"
  | CUnit -> "()"
;;

let rec frestore_imm c =
  match c with
  | ImmInt i -> string_of_int i
  | ImmBool false -> "false"
  | ImmBool true -> "true"
  | ImmNil -> "[]"
  | ImmIdentifier id -> id
  | ImmUnit -> "()"
  | ImmTuple tup -> "(" ^ String.concat ", " (List.map frestore_imm tup) ^ ")"
;;

let rec frestore_pattern pat =
  match pat with
  | PWildCard -> "_"
  | PCons (h_pat, t_pat) ->
    "(" ^ frestore_pattern h_pat ^ " :: " ^ frestore_pattern t_pat ^ ")"
  | PIdentifier x -> x
  | PTuple lst -> "(" ^ String.concat ", " (List.map frestore_pattern lst) ^ ")"
  | PConstant c -> frestore_constant c
  | PConstraint (pat, tp) -> "(" ^ frestore_pattern pat ^ " : " ^ pp_type_name tp ^ ")"
;;

let rec restore_cexpr = function
  | CImmExpr imm -> frestore_imm imm
  | CIfThenElse (cond, then_branch, else_branch) ->
    "if "
    ^ frestore_imm cond
    ^ " then "
    ^ pp_aexpr then_branch
    ^ " else "
    ^ pp_aexpr else_branch
  | CMatch (pat_head, pat_exp_lst) ->
    "match "
    ^ frestore_pattern pat_head
    ^ " with\n"
    ^ String.concat
        "\n"
        (List.map
           (fun (pat, ae) -> "| " ^ frestore_pattern pat ^ " -> " ^ pp_aexpr ae)
           pat_exp_lst)
  | CApplication (left, right) -> restore_cexpr left ^ " " ^ restore_cexpr right
  | CConstraint (imm, typ) -> "(" ^ frestore_imm imm ^ " : " ^ pp_type_name typ ^ ")"

and pp_aexpr = function
  | ACExpr cexp -> restore_cexpr cexp
  | ALetIn (pat, outer, inner) ->
    "let "
    ^ frestore_pattern pat
    ^ " = "
    ^ restore_cexpr outer
    ^ " in\n "
    ^ pp_aexpr inner
;;

let frestore_rec_flag = function
  | Rec -> "rec "
  | NotRec -> ""
;;

let restore_anf_decl = function
  | ADSingleLet (rec_flag, ALet (pat, patterns, body)) ->
    " let "
    ^ frestore_rec_flag rec_flag
    ^ frestore_pattern pat
    ^ " "
    ^ String.concat " " (List.map frestore_pattern patterns)
    ^ " = "
    ^ pp_aexpr body
  | ADMutualRecDecl (rec_flag, bindings) ->
    let rec_flag_str = frestore_rec_flag rec_flag in
    " let "
    ^ rec_flag_str
    ^ String.concat
        " and "
        (List.map
           (fun binding ->
             match binding with
             | ALet (pat, patterns, exp) ->
               frestore_pattern pat
               ^ " "
               ^ String.concat " " (List.map frestore_pattern patterns)
               ^ " = "
               ^ pp_aexpr exp)
           bindings)
;;

let restore_program declarations =
  String.concat "\n" (List.map restore_anf_decl declarations)
;;

(* let prog =
  {| let rec fib_cps n cont =
   if (n = 0) then
    cont 0
   else if (n = 1) then
     cont 1
   else
     fib_cps (n - 1) (fun a ->
     fib_cps (n - 2) (fun b ->
     cont (a + b))) |}
;;

let () =
  let rec restore_anf aux = function
    | h :: tl ->
      (match h with
       | Ok decl -> restore_anf (aux ^ restore_anf_decl decl) tl
       | Error _ -> "Error: %s\n")
    | [] -> aux
  in
  match Parser.parse_program prog with
  | Ok ast ->
    let final =
      ast |> Closure_conversion.convert_ast |> Lambda_lifting.lift_ast |> Anf.transform
    in
    let w = restore_anf "" final in
    Format.printf "%s\n" w
  | Error message -> Format.printf "Error: %s\n" message
;;
*)
