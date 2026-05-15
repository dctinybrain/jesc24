From Coq Require Import Lists.List Strings.Ascii Strings.String.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import jessica_ast quasi_json quasi_justin.

Import ListNotations.
Open Scope string_scope.

Module JessieGrammar.
  Export JessicaAst.
  Export QuasiJson.
  Export QuasiJustin.

  (* String literal: matches '...' (single quoted, no escape handling) *)
  Definition string_lit_single : pat :=
    seq (sym "'")
      (seq (star (seq (PNot (sym "'")) (PSet fullcharset)))
            (sym "'")).

  Definition string_lit : pat := tok string_lit_single.

  (* Import statement: import { x } from 'path'; *)
  Definition import_stmt : pat :=
    seq (kw "import")
      (seq (sym "{")
        (seq ident
          (seq (sym "}")
            (seq (kw "from")
              (seq string_lit (sym ";")))))).

  (* quasi-jessie.js.ts: lValue <- ... ; here narrowed to identifiers only. *)
  Definition lvalue : pat := ident.

  Definition op_assign : pat :=
    seq lvalue
      (seq (alt (sym "+=") (sym "-=")) (PNT 0)).

  Definition assign_expr : pat :=
    seq lvalue (seq (sym "=") (PNT 0)).

  Definition paren_expr : pat :=
    seq (sym "(") (seq (PNT 0) (sym ")")).

  (* quasi-jessie.js.ts: record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE *)
  Definition object_pat : pat :=
    seq (sym "{")
      (seq
        (opt
          (seq (PNT 2)
            (seq (star (seq (sym ",") (PNT 2)))
              (opt (sym ",")))))
        (sym "}")).

  Definition comma_list (elem : pat) : pat :=
    seq elem (star (seq (sym ",") elem)).

  Definition array_pat : pat :=
    seq (sym "[")
      (seq (opt (seq (comma_list (PNT 0)) (opt (sym ",")))) (sym "]")).

  Definition match_array_param : pat :=
    seq (sym "[") (seq (opt (comma_list ident)) (sym "]")).

  Definition arrow_param : pat := alt match_array_param ident.

  Definition arrow_params : pat :=
    alt ident
      (seq (sym "(") (seq (opt (comma_list arrow_param)) (sym ")"))).

  Definition arrow_body : pat :=
    alt (PNT 4)
      (alt paren_expr (PNT 0)).

  (* quasi-jessie.js.ts:
     arrowFunc <- arrowParams _NO_NEWLINE ARROW block
                / arrowParams _NO_NEWLINE ARROW assignExpr;
  *)
  Definition arrow_func : pat :=
    seq arrow_params
      (seq (sym "=>") arrow_body).

  (* quasi-jessie.js.ts:
     memberPostOp / callPostOp extensions inherited from Justin.
  *)
  Definition expr_post_op : pat := QuasiJustin.post_op 0.

  Definition less_than : pat :=
    seq (PNT 1)
      (seq (star expr_post_op)
        (seq (sym "<")
          (seq (PNT 1) (star expr_post_op)))).

  Definition const_decl : pat :=
    seq (kw "const")
      (seq ident
        (seq (sym "=")
          (seq (PNT 0) (sym ";")))).

  Definition let_decl : pat :=
    seq (kw "let")
      (seq ident
        (seq (opt (seq (sym "=") (PNT 0))) (sym ";"))).

  (* quasi-jessie.js.ts: returnStatement production subset. *)
  Definition return_stmt : pat :=
    seq (kw "return") (seq (PNT 0) (sym ";")).

  (* Throw statement: throw expr; *)
  Definition throw_stmt : pat :=
    seq (kw "throw") (seq (PNT 0) (sym ";")).

  (* If statement: if (cond) then_branch else else_branch *)
  Definition if_stmt : pat :=
    seq (kw "if")
      (seq (sym "(")
        (seq (PNT 0)  (* condition *)
          (seq (sym ")")
            (seq (PNT 4)  (* then branch - block *)
              (opt (seq (kw "else") (PNT 4))))))).

  (* quasi-jessie.js.ts: exprStatement <- ~cantStartExprStatement expr SEMI. *)
  Definition expr_stmt : pat := seq (PNT 0) (sym ";").

  Definition assert_stmt : pat :=
    seq (kw "assert")
      (seq (sym "(")
        (seq (PNT 0)
          (seq (sym ")") (sym ";")))).

  (* quasi-jessie.js.ts: block production subset. *)
  Definition block : pat :=
    seq (sym "{") (seq (star (PNT 3)) (sym "}")).

  Definition grammar : Syntax.grammar :=
    [ (* 0 expr *)
      (* quasi-jessie.js.ts: assignExpr production subset. *)
      alt arrow_func
        (alt op_assign
          (alt assign_expr
            (alt less_than
              (alt (seq (sym "!") (PNT 0)) (* !expr *)
                (seq (PNT 1) (star expr_post_op))))));
      (* 1 primaryExpr *)
      (* quasi-jessie.js.ts: primaryExpr inherits Justin primaryExpr. *)
      alt string_lit
        (alt number
          (alt array_pat
            (alt object_pat
              (alt paren_expr ident))));
      (* 2 propDef *)
      seq (alt ident number) (seq (sym ":") (PNT 0));
      (* 3 statement *)
      (* quasi-jessie.js.ts: binding / import / if / throw / exprStatement / declOp subset. *)
      alt if_stmt
        (alt import_stmt
          (alt throw_stmt
            (alt const_decl
              (alt let_decl
                (alt return_stmt
                  (alt assert_stmt expr_stmt))))));
      (* 4 block / arrow body block *)
      block;
      (* 5 module body *)
      (* quasi-jessie.js.ts: start production subset. *)
      seq ws (seq (star (PNT 3)) (seq ws eof))
    ].

  Definition expr : pat := PNT 0.
  Definition statement : pat := PNT 3.
  Definition moduleBody : pat := PNT 5.
  Definition exact_module_source (src : string) : pat :=
    seq ws (seq (string_pat src) (seq ws eof)).

End JessieGrammar.
