(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

(* Restricted language *)

open Ast

(* Immediate values *)
type immexpr =
  | ImmediateInt of int 
  | ImmediateBool of bool 
  | ImmediateUnit
  | ImmediateNil
  | ImmediateIdentifier of string 
  | ImmediateTuple of aexpr list
  | ImmediateFunc of pattern * aexpr
[@@deriving show { with_path = false }]

(* cexprs *)
and cexpr =
  | CApp of immexpr * immexpr 
  | CImmExpr of immexpr 
[@@deriving show { with_path = false }]

(* Anf expressions *)
and aexpr =
  | ANFLetIn of rec_flag * pattern * cexpr * aexpr
  | ANFIfThenElse of aexpr * aexpr * aexpr 
  | ANFCEexpr of cexpr 
  | ANFTuple of aexpr list
  | ANFMatch of pattern * (pattern * aexpr) list
  | ANFConstraint of aexpr * type_name
[@@deriving show { with_path = false }]

(* Anf declarations *)
type anf_single_let = ANFDec of pattern * aexpr [@@deriving show { with_path = false }]

type anf_let_declaration =
  | ANFSingleLet of rec_flag * anf_single_let
  | ANFMutualRecDecl of rec_flag * anf_single_let list
[@@deriving show { with_path = false }]
(** Statements type (list of top level declarations) *)
type anf_declarations = anf_let_declaration list [@@deriving show { with_path = false }]
