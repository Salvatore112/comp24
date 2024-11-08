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

let%expect_test _ =
  test_ast
    [ ANFSingleLet
        ( NotRec
        , ANFDec
            ( PIdentifier "x"
            , ANFLetIn
                ( NotRec
                , PIdentifier "$ANF_VAR$1"
                , CApp (ImmediateIdentifier "( + )", ImmediateInt 53)
                , ANFLetIn
                    ( NotRec
                    , PIdentifier "$ANF_VAR$2"
                    , CApp (ImmediateIdentifier "$ANF_VAR$1", ImmediateInt 27)
                    , ANFLetIn
                        ( NotRec
                        , PIdentifier "$ANF_VAR$3"
                        , CApp
                            ( ImmediateTuple
                                [ ANFCEexpr (CImmExpr (ImmediateInt 1))
                                ; ANFLetIn
                                    ( NotRec
                                    , PIdentifier "$ANF_VAR$1"
                                    , CApp (ImmediateIdentifier "( + )", ImmediateInt 2)
                                    , ANFLetIn
                                        ( NotRec
                                        , PIdentifier "$ANF_VAR$2"
                                        , CApp
                                            ( ImmediateIdentifier "$ANF_VAR$1"
                                            , ImmediateInt 6 )
                                        , ANFCEexpr
                                            (CImmExpr (ImmediateIdentifier "$ANF_VAR$2"))
                                        ) )
                                ; ANFCEexpr (CImmExpr (ImmediateInt 3))
                                ]
                            , ImmediateIdentifier "$ANF_VAR$2" )
                        , ANFCEexpr (CImmExpr (ImmediateIdentifier "$ANF_VAR$3")) ) ) ) )
        )
    ];
  [%expect
    {|
    [(DSingleLet (NotRec,
        (DLet ((PIdentifier "x"),
           (ELetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
              (EApplication ((EIdentifier "( + )"), (EConstant (CInt 53)))),
              (ELetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                 (EApplication ((EIdentifier "$ANF_VAR$1"), (EConstant (CInt 27))
                    )),
                 (ELetIn (NotRec, (PIdentifier "$ANF_VAR$3"),
                    (EApplication (
                       (ETuple
                          [(EConstant (CInt 1));
                            (ELetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
                               (EApplication ((EIdentifier "( + )"),
                                  (EConstant (CInt 2)))),
                               (ELetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                                  (EApplication ((EIdentifier "$ANF_VAR$1"),
                                     (EConstant (CInt 6)))),
                                  (EIdentifier "$ANF_VAR$2")))
                               ));
                            (EConstant (CInt 3))]),
                       (EIdentifier "$ANF_VAR$2"))),
                    (EIdentifier "$ANF_VAR$3")))
                 ))
              ))
           ))
        ))
      ]
    |}]
;;
