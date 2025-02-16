(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Ast

type cexpr =
  | CApplication of cexpr * cexpr
  | CIfThenElse of Middleend.Anf_ast.immexpr * aexpr * aexpr
  | CImmExpr of Middleend.Anf_ast.immexpr

and aexpr =
  | ALetIn of string * aexpr * aexpr
  | ACExpr of cexpr

type single_pe_binding =
  | AFunLet of string * string list * aexpr
  | ANotFunLet of string * aexpr

type pe_decl =
  | ADSingleLet of rec_flag * single_pe_binding
  | ADMutualRecDecl of rec_flag * single_pe_binding list (**List.length >= 2 *)

type pe_prog = pe_decl list
