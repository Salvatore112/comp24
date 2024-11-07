(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

open Ast
open Anf

let%expect_test _ =
  test_prog
    [ DSingleLet
        ( NotRec
        , DLet
            ( PIdentifier "test"
            , EApplication
                ( EFunction
                    ( PIdentifier "x"
                    , EApplication
                        ( EApplication (EIdentifier "( + )", EIdentifier "x")
                        , EConstant (CInt 1) ) )
                , EConstant (CInt 2) ) ) )
    ];
  [%expect
    {|
    [(ANFSingleLet (NotRec,
        (ANFDec ((PIdentifier "test"),
           (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$3"),
              (CApp (
                 (ImmediateFunc ((PIdentifier "x"),
                    (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
                       (CApp ((ImmediateIdentifier "( + )"),
                          (ImmediateIdentifier "x"))),
                       (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                          (CApp ((ImmediateIdentifier "$ANF_VAR$1"),
                             (ImmediateInt 1))),
                          (ANFCEexpr
                             (CImmExpr (ImmediateIdentifier "$ANF_VAR$2")))
                          ))
                       ))
                    )),
                 (ImmediateInt 2))),
              (ANFCEexpr (CImmExpr (ImmediateIdentifier "$ANF_VAR$3")))))
           ))
        ))
      ] |}]
;;

let%expect_test _ =
  test_prog
    [ DSingleLet
        ( NotRec
        , DLet
            ( PIdentifier "x"
            , EApplication
                ( EApplication (EIdentifier "map", EIdentifier "lam")
                , EApplication
                    ( EApplication (EIdentifier "( :: )", EConstant (CInt 1))
                    , EApplication
                        ( EApplication (EIdentifier "( :: )", EConstant (CInt 2))
                        , EApplication
                            ( EApplication (EIdentifier "( :: )", EConstant (CInt 3))
                            , EConstant CNil ) ) ) ) ) )
    ];
  [%expect
    {|
    [(ANFSingleLet (NotRec,
        (ANFDec ((PIdentifier "x"),
           (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
              (CApp ((ImmediateIdentifier "map"), (ImmediateIdentifier "lam"))),
              (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                 (CApp ((ImmediateIdentifier "( :: )"), (ImmediateInt 1))),
                 (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$3"),
                    (CApp ((ImmediateIdentifier "( :: )"), (ImmediateInt 2))),
                    (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$4"),
                       (CApp ((ImmediateIdentifier "( :: )"), (ImmediateInt 3))),
                       (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$5"),
                          (CApp ((ImmediateIdentifier "$ANF_VAR$4"), ImmediateNil
                             )),
                          (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$6"),
                             (CApp ((ImmediateIdentifier "$ANF_VAR$3"),
                                (ImmediateIdentifier "$ANF_VAR$5"))),
                             (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$7"),
                                (CApp ((ImmediateIdentifier "$ANF_VAR$2"),
                                   (ImmediateIdentifier "$ANF_VAR$6"))),
                                (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$8"),
                                   (CApp ((ImmediateIdentifier "$ANF_VAR$1"),
                                      (ImmediateIdentifier "$ANF_VAR$7"))),
                                   (ANFCEexpr
                                      (CImmExpr
                                         (ImmediateIdentifier "$ANF_VAR$8")))
                                   ))
                                ))
                             ))
                          ))
                       ))
                    ))
                 ))
              ))
           ))
        ))
      ] |}]
;;

let%expect_test _ =
  test_prog
    [ DSingleLet
        ( NotRec
        , DLet
            ( PIdentifier "x"
            , EMatch
                ( PIdentifier "x"
                , [ ( PConstant (CInt 1)
                    , EApplication
                        ( EApplication (EIdentifier "( + )", EConstant (CInt 2))
                        , EConstant (CInt 3) ) )
                  ; ( PConstant (CInt 2)
                    , EApplication
                        ( EApplication (EIdentifier "( + )", EConstant (CInt 4))
                        , EConstant (CInt 5) ) )
                  ] ) ) )
    ];
  [%expect
    {|
    [(ANFSingleLet (NotRec,
        (ANFDec ((PIdentifier "x"),
           (ANFMatch ((PIdentifier "x"),
              [((PConstant (CInt 1)),
                (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
                   (CApp ((ImmediateIdentifier "( + )"), (ImmediateInt 2))),
                   (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                      (CApp ((ImmediateIdentifier "$ANF_VAR$1"), (ImmediateInt 3)
                         )),
                      (ANFCEexpr (CImmExpr (ImmediateIdentifier "$ANF_VAR$2")))))
                   )));
                ((PConstant (CInt 2)),
                 (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
                    (CApp ((ImmediateIdentifier "( + )"), (ImmediateInt 4))),
                    (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                       (CApp ((ImmediateIdentifier "$ANF_VAR$1"),
                          (ImmediateInt 5))),
                       (ANFCEexpr (CImmExpr (ImmediateIdentifier "$ANF_VAR$2")))
                       ))
                    )))
                ]
              ))
           ))
        ))
      ] |}]
;;

let%expect_test _ =
  test_prog
    [ DSingleLet
        ( NotRec
        , DLet
            ( PIdentifier "x"
            , EApplication
                ( EFunction
                    ( PIdentifier "x"
                    , EApplication
                        ( EApplication (EIdentifier "( + )", EIdentifier "x")
                        , EConstant (CInt 1) ) )
                , EConstant (CInt 65) ) ) )
    ];
  [%expect
    {|
    [(ANFSingleLet (NotRec,
        (ANFDec ((PIdentifier "x"),
           (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$3"),
              (CApp (
                 (ImmediateFunc ((PIdentifier "x"),
                    (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$1"),
                       (CApp ((ImmediateIdentifier "( + )"),
                          (ImmediateIdentifier "x"))),
                       (ANFLetIn (NotRec, (PIdentifier "$ANF_VAR$2"),
                          (CApp ((ImmediateIdentifier "$ANF_VAR$1"),
                             (ImmediateInt 1))),
                          (ANFCEexpr
                             (CImmExpr (ImmediateIdentifier "$ANF_VAR$2")))
                          ))
                       ))
                    )),
                 (ImmediateInt 65))),
              (ANFCEexpr (CImmExpr (ImmediateIdentifier "$ANF_VAR$3")))))
           ))
        ))
      ] |}]
;;
