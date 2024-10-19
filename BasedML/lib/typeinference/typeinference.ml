(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)
include StatementInfer

open Constraint

let const2type : Ast.constant -> Ast.typeName = function
  | Ast.CBool _ -> Ast.TBool
  | Ast.CInt _ -> Ast.TInt
;;

type patern_mode =
  | PMAdd
  | PMCheck

let infer_pattern : patern_mode -> Ast.pattern -> (state, Ast.typeName) t =
  fun pm cpat ->
  let get_pat_and_type = function
    | Ast.PNConstraint pat -> fresh_tv >>= fun t -> return (pat, t)
    | Ast.PConstraint (pat, tp) -> return (pat, tp)
  in
  let infer_add_pident name tp =
    let* var_tp = read_var_type name in
    match var_tp with
    | None -> write_flat_var_type name tp *> return tp
    | Some _ ->
      fail (Format.sprintf "Variable %s is bound several times in this matching" name)
  and infer_add_pconstant c tp =
    let const_tp = const2type c in
    write_constr (create_constr tp const_tp) *> return const_tp
  and infer_add_ptupple p_lst tp rec_fun =
    let* t_lst = map_list rec_fun p_lst in
    let tuple_tp = Ast.TTuple t_lst in
    write_constr (create_constr tp tuple_tp) *> return tuple_tp
  and infer_add_pcons (p_head, p_tail) tp rec_fun =
    let* head_tp = rec_fun p_head in
    let* tail_tp = rec_fun p_tail in
    write_constr (create_constr tp tail_tp)
    *> write_constr (create_constr (Ast.TList head_tp) tail_tp)
    *> return tail_tp
  and infer_add_pnil tp =
    let* tv = fresh_tv in
    let list_tp = Ast.TList tv in
    write_constr (create_constr tp list_tp) *> return list_tp
  in
  let rec help cp =
    let* pat, tp = get_pat_and_type cp in
    match pat with
    | Ast.PIdentifier name -> infer_add_pident name tp
    | Ast.PConstant c -> infer_add_pconstant c tp
    | Ast.PTuple p_lst -> infer_add_ptupple p_lst tp help_no_constraint
    | Ast.PCons (p_head, p_tail) -> infer_add_pcons (p_head, p_tail) tp help_no_constraint
    | Ast.PNil -> infer_add_pnil tp
    | Ast.PWildCard -> return tp
  and help_no_constraint ncp = help (PNConstraint ncp) in
  let* glob_env = read_env in
  write_env MapString.empty
  *> let* tp = help cpat in
     let* loc_env = read_env in
     match pm with
     | PMAdd ->
       let new_env =
         MapString.merge
           (fun _ old_el new_el ->
             match new_el with
             | Some x -> Some x
             | None -> old_el)
           glob_env
           loc_env
       in
       write_env new_env *> return tp
     | PMCheck ->
       let not_found =
         MapString.fold
           (fun name _ acc ->
             match acc with
             | None when not (MapString.mem name glob_env) -> Some name
             | x -> x)
           loc_env
           None
       in
       (match not_found with
        | None -> write_env glob_env *> return tp
        | Some x -> fail (Format.sprintf "Unbound value %s" x))
;;

let rec infer_expr : Ast.expr -> (state, Ast.typeName) t = function
  | Ast.EConstant c -> return (const2type c)
  | Ast.EIdentifier name -> infer_ident name
  | Ast.ENil ->
    let* tv = fresh_tv in
    return (Ast.TList tv)
  | Ast.EFunction (arg, body) -> infer_func arg body
  | Ast.EApplication (fun_exp, arg_exp) -> infer_app fun_exp arg_exp
  | Ast.EIfThenElse (e1, e2, e3) -> infer_ifthenelse e1 e2 e3
  | Ast.ELetIn (_rec_flag, _pattern, _expr_val, _expr_in) ->
    fail "boba should be implemented"
  | Ast.ETuple exp_lst ->
    let* t_lst = map_list infer_expr exp_lst in
    return (Ast.TTuple t_lst)
  | Ast.EMatch (scrutin, pat_exp_lst) -> infer_match scrutin pat_exp_lst
  | Ast.EConstraint (exp, tp) ->
    let* exp_tp = infer_expr exp in
    write_constr (create_constr exp_tp tp) *> return exp_tp

and infer_ident : string -> (state, Ast.typeName) t =
  fun name ->
  let* vt_opt = read_var_type name in
  match vt_opt with
  | None -> fail (Format.sprintf "Unbound value: %s" name)
  | Some tp -> return tp

and infer_func : Ast.pattern -> Ast.expr -> (state, Ast.typeName) t =
  fun pat exp ->
  let* arg_tp = infer_pattern PMAdd pat in
  let* exp_tp = infer_expr exp in
  let fcn_tp = Ast.TFunction (arg_tp, exp_tp) in
  return fcn_tp

and infer_app : Ast.expr -> Ast.expr -> (state, Ast.typeName) t =
  fun func_exp args_exp ->
  let* self_tp = fresh_tv in
  let* func_tp = infer_expr func_exp in
  let* arg_tp = infer_expr args_exp in
  write_constr (create_constr func_tp (Ast.TFunction (arg_tp, self_tp))) *> return self_tp

and infer_ifthenelse : Ast.expr -> Ast.expr -> Ast.expr -> (state, Ast.typeName) t =
  fun e1 e2 e3 ->
  let* tp = fresh_tv in
  let* cur_env = read_env in
  let* t1 = infer_expr e1 <* write_env cur_env in
  let* t2 = infer_expr e2 <* write_env cur_env in
  let* t3 = infer_expr e3 <* write_env cur_env in
  write_constr (create_constr t1 Ast.TInt)
  *> write_constr (create_constr tp t2)
  *> write_constr (create_constr tp t3)
  *> return tp

and infer_match : Ast.pattern -> (Ast.pattern * Ast.expr) list -> (state, Ast.typeName) t =
  fun scrutin pat_exp_lst ->
  let* tp = fresh_tv in
  let* scr_tp = infer_pattern PMCheck scrutin in
  let* cur_env = read_env in
  let help (pat, exp) =
    let* pat_tp = infer_pattern PMAdd pat in
    let* exp_tp = infer_expr exp in
    write_constr (create_constr pat_tp scr_tp)
    *> write_constr (create_constr exp_tp tp)
    *> return ()
    <* write_env cur_env
  in
  map_list help pat_exp_lst *> return tp
;;

let test_infer_exp string_exp =
  let res = Parser.parse Parser.p_exp string_exp in
  match res with
  | Result.Ok exp ->
    let (env, constrs, _), res =
      run (infer_expr exp) (MapString.empty, ConstraintSet.empty, 0)
    in
    (match res with
     | Result.Ok tp ->
       Format.printf
         "res: %s @\nenv: %s@\n constrs: %s"
         (Ast.show_typeName tp)
         (show_env_map env)
         (show_constr_set constrs)
     | Result.Error s -> Format.printf "Infer error: %s" s)
  | Result.Error e -> Format.printf "Parser error: %s" e
;;

let%expect_test _ =
  test_infer_exp "fun ((x, y): (int*bool)) -> y";
  [%expect
    {|
    res: (TFunction ((TTuple [(TPoly "_p0"); (TPoly "_p1")]), (TPoly "_p1")))
    env: [""x"": (TFFlat (TPoly "_p0")),
     ""y"": (TFFlat (TPoly "_p1")),
     ]
     constrs: [((TTuple [TInt; TBool]), (TTuple [(TPoly "_p0"); (TPoly "_p1")]))
     ] |}]
;;

let%expect_test _ =
  test_infer_exp "fun ((x::y): (int list)) -> y";
  [%expect
    {|
    res: (TFunction ((TPoly "_p1"), (TPoly "_p1")))
    env: [""x"": (TFFlat (TPoly "_p0")),
     ""y"": (TFFlat (TPoly "_p1")),
     ]
     constrs: [((TPoly "_p1"), (TList TInt))
     ((TPoly "_p1"), (TList (TPoly "_p0")))
     ] |}]
;;

let%expect_test _ =
  test_infer_exp {|fun f list -> match list with
  | [] -> list
  | h :: tl -> h|};
  [%expect {|
    res: (TFunction ((TPoly "_p0"), (TFunction ((TPoly "_p1"), (TPoly "_p2")))))
    env: [""f"": (TFFlat (TPoly "_p0")),
     ""list"": (TFFlat (TPoly "_p1")),
     ]
     constrs: [((TPoly "_p1"), (TPoly "_p2"))
     ((TPoly "_p2"), (TPoly "_p7"))
     ((TPoly "_p3"), (TPoly "_p8"))
     ((TPoly "_p3"), (TList (TPoly "_p5")))
     ((TPoly "_p4"), (TList (TPoly "_p5")))
     ((TPoly "_p6"), (TPoly "_p8"))
     ((TPoly "_p8"), (TList (TPoly "_p7")))
     ] |}]
;;

let%expect_test _ =
  test_infer_exp {|fun f list -> match nolist with
  | [] -> list
  | h :: tl -> h|};
  [%expect {| Infer error: Unbound value nolist |}]
;;

