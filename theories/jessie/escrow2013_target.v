From Coq Require Import List String ZArith.
From iris.jessie Require Import jessica_ast.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module Escrow2013Target.
  Import JessicaAst.

  (* Constructor-rich JessicaAst target for the current escrow2013 rendition.
     This is intended to track the same underlying structure as the in-tree
     escrow2013.jessie.json / escrow2013.jessie.lisp artifacts, just rendered
     with JessieAst constructors instead of JSON or Lisp surface syntax. *)

  Definition u (x : string) : jexpr := JUse x.
  Definition s (x : string) : jexpr := JDataString x.
  Definition n (x : Z) : jexpr := JDataNum x.
  Definition arr (xs : list jexpr) : jexpr := JArray xs.
  Definition def (x : string) : jpat := JDef x.
  Definition bind (x : string) (rhs : jexpr) : jbind := JBind (def x) rhs.
  Definition bind_pat (p : jpat) (rhs : jexpr) : jbind := JBind p rhs.
  Definition prop (name : string) (value : jexpr) : jprop := JProp name value.
  Definition get (obj : jexpr) (field : string) : jexpr := JGet obj field.
  Definition call (callee : jexpr) (args : list jexpr) : jexpr := JCall callee args.
  Definition callm (obj : jexpr) (field : string) (args : list jexpr) : jexpr :=
    JCall (JGet obj field) args.
  Definition arrow (params : list jpat) (ss : list jstmt) : jexpr :=
    JArrow params (JBodyBlock ss).
  Definition arrow_expr (params : list jpat) (e : jexpr) : jexpr :=
    JArrow params (JBodyExpr e).
  Definition lambda (params : list jpat) (ss : list jstmt) : jexpr :=
    JLambda params (JBodyBlock ss).
  Definition not_ (e : jexpr) : jexpr := JPreOp "!" e.

  Definition qjoin_body : list jstmt :=
    [ JReturn
        (callm
          (callm (u "Q") "all" [arr [u "p1"; u "p2"]])
          "then"
          [ arrow
              [JMatchArray [def "r1"; def "r2"]]
              [ JIf
                  (not_ (callm (u "Object") "is" [u "r1"; u "r2"]))
                  [JThrow (call (u "Error") [s "join failed"])]
                  None;
                JReturn (u "r1")
              ]
          ])
    ].

  Definition qjoin_expr : jexpr :=
    callm
      (callm (u "Q") "all" [arr [u "p1"; u "p2"]])
      "then"
      [ arrow
          [JMatchArray [def "r1"; def "r2"]]
          [ JIf
              (not_ (callm (u "Object") "is" [u "r1"; u "r2"]))
              [JThrow (call (u "Error") [s "join failed"])]
              None;
            JReturn (u "r1")
          ]
      ].

  Definition transfer_body : list jstmt :=
    [ JConstStmt
        [ bind
            "makeEscrowPurseP"
            (call (u "Qjoin")
              [ get (callm (u "E") "get" [u "srcPurseP"]) "makePurse";
                get (callm (u "E") "get" [u "dstPurseP"]) "makePurse"
              ])
        ];
      JConstStmt
        [ bind
            "escrowPurseP"
            (call (call (u "E") [u "makeEscrowPurseP"]) [])
        ];
      JExprStmt
        (callm
          (call (u "Q") [u "decisionP"])
          "then"
          [ arrow [def "_"]
              [ JExprStmt
                  (callm
                    (call (u "E") [u "dstPurseP"])
                    "deposit"
                    [u "amount"; u "escrowPurseP"])
              ];
            arrow [def "_"]
              [ JExprStmt
                  (callm
                    (call (u "E") [u "srcPurseP"])
                    "deposit"
                    [u "amount"; u "escrowPurseP"])
              ]
          ]);
      JReturn
        (callm
          (call (u "E") [u "escrowPurseP"])
          "deposit"
          [u "amount"; u "srcPurseP"])
    ].

  Definition failOnly_body : list jstmt :=
    [ JReturn
        (callm
          (call (u "Q") [u "cancellationP"])
          "then"
          [ arrow [def "cancellation"]
              [JThrow (u "cancellation")]
          ])
    ].

  Definition failOnly_expr : jexpr :=
    callm
      (call (u "Q") [u "cancellationP"])
      "then"
      [ arrow [def "cancellation"]
          [JThrow (u "cancellation")]
      ].

  Definition escrowExchange_body : list jstmt :=
    [ JLetNames [def "decide"];
      JConstStmt
        [ bind
            "decisionP"
            (callm
              (u "Q")
              "promise"
              [ arrow [def "resolve"]
                  [JExprStmt (JAssign (u "decide") (u "resolve"))]
              ])
        ];
      JExprStmt
        (call
          (u "decide")
          [ callm
              (u "Q")
              "race"
              [ arr
                  [ callm
                      (u "Q")
                      "all"
                      [ arr
                          [ call (u "transfer")
                              [ u "decisionP";
                                get (u "a") "moneySrcP";
                                get (u "b") "moneyDstP";
                                get (u "b") "moneyNeeded"
                              ];
                            call (u "transfer")
                              [ u "decisionP";
                                get (u "b") "stockSrcP";
                                get (u "a") "stockDstP";
                                get (u "a") "stockNeeded"
                              ]
                          ]
                      ];
                    call (u "failOnly") [get (u "a") "cancellationP"];
                    call (u "failOnly") [get (u "b") "cancellationP"]
                  ]
              ]
          ]);
      JReturn (u "decisionP")
    ].

  Definition escrow2013_program : jmodule :=
    JModule
      [ JImport [JImportAs "E" "E"] "@endo/far";
        JConst [bind "Q" (u "Promise")];
        JConst
          [ bind
              "Qjoin"
              (call (u "harden")
                [ arrow_expr [def "p1"; def "p2"] qjoin_expr ])
          ];
        JConst
          [ bind
              "transfer"
              (call (u "harden")
                [ JArrow
                    [def "decisionP"; def "srcPurseP"; def "dstPurseP"; def "amount"]
                    (JBodyBlock transfer_body) ])
          ];
        JConst
          [ bind
              "failOnly"
              (call (u "harden")
                [ arrow_expr [def "cancellationP"] failOnly_expr ])
          ];
        JConst
          [ bind
              "escrowExchange"
              (call (u "harden")
                [ JArrow [def "a"; def "b"] (JBodyBlock escrowExchange_body) ])
          ]
      ].
End Escrow2013Target.
