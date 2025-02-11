(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Ast
open Base
open Utils

let rec close_function lts local_ctx global_ctx convert = function
  | EFunction (pat, body) ->
    EFunction (pat, close_function lts local_ctx global_ctx convert body)
  | expr -> convert lts local_ctx global_ctx expr
;;

let convert global_ctx declaration =
  let rec helper lts local_ctx global_ctx = function
    | EConstant const -> EConstant const
    | EIdentifier id ->
      (match Map.find local_ctx id with
       | Some free ->
         let ids = List.map (Set.to_list free) ~f:(fun x -> EIdentifier x) in
         List.fold_left ids ~f:(fun f arg -> EApplication (f, arg)) ~init:(EIdentifier id)
       | None -> EIdentifier id)
    | EFunction (pat, body) ->
      let unbound_names = unbound_identifiers (EFunction (pat, body)) in
      let unbound_names_without_global =
        Set.diff (Set.diff unbound_names global_ctx) infix_ops_set
      in
      let unbound_ids_patterns =
        List.map (Set.to_list unbound_names_without_global) ~f:(fun x -> PIdentifier x)
      in
      let unbound_ids_exps =
        List.map (Set.to_list unbound_names_without_global) ~f:(fun x -> EIdentifier x)
      in
      let closed_fun =
        close_function
          lts
          local_ctx
          (Set.diff global_ctx infix_ops_set)
          helper
          (EFunction (pat, body))
      in
      let new_fun =
        List.fold_right
          ~f:(fun pat exp -> EFunction (pat, exp))
          unbound_ids_patterns
          ~init:closed_fun
      in
      List.fold_left
        unbound_ids_exps
        ~f:(fun f arg -> EApplication (f, arg))
        ~init:new_fun
    | EApplication (left, right) ->
      EApplication
        ( helper lts local_ctx (Set.diff (Set.diff global_ctx lts) infix_ops_set) left
        , helper lts local_ctx (Set.diff (Set.diff global_ctx lts) infix_ops_set) right )
    | EIfThenElse (guard, then_branch, else_branch) ->
      let global_ctx = Set.diff global_ctx infix_ops_set in
      EIfThenElse
        ( helper lts local_ctx (Set.diff global_ctx infix_ops_set) guard
        , helper lts local_ctx (Set.diff global_ctx infix_ops_set) then_branch
        , helper lts local_ctx (Set.diff global_ctx infix_ops_set) else_branch )
    | ELetIn (rec_flag, pat, outer, inner) ->
      (match pat, outer with
       (* Inner fun *)
       | PIdentifier id, EFunction (_, _) ->
         let updated_lts = Set.add lts id in
         let updated_global_env =
           match rec_flag with
           | Rec -> Set.add (Set.diff global_ctx infix_ops_set) id
           | NotRec -> Set.add (Set.diff global_ctx infix_ops_set) id
         in
         let unbound_names = unbound_identifiers (ELetIn (rec_flag, pat, outer, inner)) in
         let unbound_names_without_global =
           Set.diff (Set.diff unbound_names updated_global_env) infix_ops_set
         in
         let closed_fun = close_function lts local_ctx updated_global_env helper outer in
         let unbound_ids_without_global =
           List.map (Set.to_list unbound_names_without_global) ~f:(fun x -> PIdentifier x)
         in
         let closed_outer =
           List.fold_right
             unbound_ids_without_global
             ~f:(fun pat exp -> EFunction (pat, exp))
             ~init:closed_fun
         in
         let updated_local_env =
           Map.set local_ctx ~key:id ~data:unbound_names_without_global
         in
         let closed_inner =
           helper
             updated_lts
             updated_local_env
             (Set.diff (Set.add global_ctx id) infix_ops_set)
             inner
         in
         let updated_outer =
           helper
             updated_lts
             updated_local_env
             (Set.diff (Set.add global_ctx id) infix_ops_set)
             closed_outer
         in
         ELetIn (rec_flag, PIdentifier id, updated_outer, closed_inner)
       | _ ->
         ELetIn
           ( rec_flag
           , pat
           , helper lts local_ctx (Set.diff global_ctx infix_ops_set) outer
           , helper lts local_ctx (Set.diff global_ctx infix_ops_set) inner ))
    | ETuple exps ->
      let new_exps =
        List.map exps ~f:(helper lts local_ctx (Set.diff global_ctx infix_ops_set))
      in
      ETuple new_exps
    | EMatch (pat, branches) ->
      let new_branches =
        List.map branches ~f:(fun (pat, exp) ->
          pat, helper lts local_ctx (Set.diff global_ctx infix_ops_set) exp)
      in
      EMatch (pat, new_branches)
    | EConstraint (exp, type_name) ->
      EConstraint (helper lts local_ctx (Set.diff global_ctx infix_ops_set) exp, type_name)
  in
  let close_declaration global_ctx = function
    | DSingleLet (flag, DLet (pat, exp)) ->
      DSingleLet
        ( flag
        , DLet
            ( pat
            , close_function
                ((module String) |> Set.empty)
                ((module String) |> Map.empty)
                (Set.diff global_ctx infix_ops_set)
                helper
                exp ) )
    | DMutualRecDecl (flag, decls) ->
      let rec handle_mutual_rec global_ctx = function
        | [] -> [], Set.diff global_ctx infix_ops_set
        | DLet (pat, exp) :: tl ->
          let closed_exp =
            close_function
              ((module String) |> Set.empty)
              (Map.empty (module String))
              (Set.diff global_ctx infix_ops_set)
              helper
              exp
          in
          let new_decl, new_env = handle_mutual_rec global_ctx tl in
          DLet (pat, closed_exp) :: new_decl, new_env
      in
      let new_decls, _ = handle_mutual_rec global_ctx decls in
      DMutualRecDecl (flag, new_decls)
  in
  close_declaration global_ctx declaration
;;

let convert_ast ast =
  let close ast =
    List.fold_left
      ast
      ~init:([], (module String) |> Set.empty)
      ~f:(fun (acc, ctx) ->
        function
        | DSingleLet (flag, DLet (pat, body)) ->
          ( convert ctx (DSingleLet (flag, DLet (pat, body))) :: acc
          , Set.union ctx (collect_names_from_patterns pat) )
        | DMutualRecDecl (flag, decls) ->
          convert ctx (DMutualRecDecl (flag, decls)) :: acc, ctx)
  in
  let converted_ast, _ = ast |> close in
  converted_ast |> List.rev
;;

let test_closure_convert ast =
  let converted = convert_ast ast in
  Stdlib.Format.printf "%s" (Ast.show_declarations converted)
;;
