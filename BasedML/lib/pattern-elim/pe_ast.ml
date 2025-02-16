(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Ast

type pe_expr =
  | CApplication of pe_expr * pe_expr
  | CIfThenElse of Middleend.Anf_ast.immexpr * pe_expr * pe_expr
  | CImmExpr of Middleend.Anf_ast.immexpr
  | ALetIn of string * pe_expr * pe_expr

type single_pe_binding =
  | AFunLet of string * string list * pe_expr
  | ANotFunLet of string * pe_expr

type pe_decl =
  | ADSingleLet of rec_flag * single_pe_binding
  | ADMutualRecDecl of single_pe_binding list (**List.length >= 2 *)

type pe_prog = pe_decl list
