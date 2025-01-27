(** Copyright 2024-2025, KreML Compiler Commutnity *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast

let access_closure = "access_closure"
let access_tuple = "access_tuple"
let list_cons = "list_cons"
let list_head = "list_head"
let list_tail = "list_tail"

let runtime_error s =
  let msg = Format.asprintf "Runtime error: %s" s in
  Expr_app (Expr_var msg, Expr_const Const_unit)
;;

let runtime_funs = [ access_closure; access_tuple; list_cons; list_head; list_tail ]

let is_runtime_fun f =
  match List.find_opt (( = ) f) runtime_funs with
  | Some _ -> true
  | None -> false
;;

let print_int = "print_int"
let stdlib_funs = [ print_int ]

let is_stdlib_fun f =
  match List.find_opt (( = ) f) stdlib_funs with
  | Some _ -> true
  | None -> false
;;
