(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Format
open Pattern_elim.Pe_ast

let rec expr_to_str ppf (expr : pe_expr) =
  match expr with
  | CApplication (func, arg) ->
    fprintf ppf "(%a %a)" expr_to_str func expr_to_str arg
  | CIfThenElse (cond, then_expr, else_expr) ->
    fprintf
      ppf
      "(if %s then %a else %a)"
      (Middleend.Anf_to_str.imm_to_string cond)
      expr_to_str
      then_expr
      expr_to_str
      else_expr
  | CImmExpr imm -> fprintf ppf "(%s)" (Middleend.Anf_to_str.imm_to_string imm)
  | ALetIn (var, value, body) ->
    fprintf ppf "(let %s = %a in %a)" var expr_to_str value expr_to_str body
;;

let binding_to_str ppf (binding : single_pe_binding) =
  match binding with
  | AFunLet (name, args, body) ->
    let args_str = String.concat " " args in
    fprintf ppf "%s %s = %a" name args_str expr_to_str body
  | ANotFunLet (name, value) -> fprintf ppf "%s = %a" name expr_to_str value
;;

let decl_to_str ppf (decl : pe_decl) =
  match decl with
  | ADSingleLet (rec_flag, binding) ->
    let rec_prefix = if rec_flag = Rec then "rec " else "" in
    fprintf ppf "let %s %a;;\n" rec_prefix binding_to_str binding
  | ADMutualRecDecl bindings ->
    let print_several_bindigs ppf bindings =
      List.iteri
        (fun i pat ->
          if i <> 0 then Format.fprintf ppf "\nand" else ();
          binding_to_str ppf pat)
        bindings
    in
    fprintf ppf "let rec %a;;\n" print_several_bindigs bindings
;;

let prog_to_str ppf (prog : pe_prog) =
  List.iter (fun decl -> fprintf ppf "%a" decl_to_str decl) prog
;;
