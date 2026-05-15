From Coq Require Import Lists.List Strings.Ascii Strings.String.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import jessica_ast quasi_json quasi_justin.

Import ListNotations.
Open Scope string_scope.

(*
  Jessie PEG grammar, mirroring the TypeScript PEG at:

    https://github.com/endojs/Jessie/blob/main/packages/parse/src/quasi-jessie.js.ts

  Each Coq rule corresponds to a production in that file.  The non-terminal
  indices (PNT n) map directly to the grammar list at the bottom of this module.

  Notation:
    a >> b   — sequence  (PEG adjacency)
    a /// b  — choice    (PEG /)
*)

Module JessieGrammar.
  Export JessicaAst.
  Export QuasiJson.
  Export QuasiJustin.

  (* ── Sequencing notation ──────────────────────────────────────── *)
  Notation "p >> q" := (PSequence p q)
    (at level 69, right associativity).

  Notation "p /// q" := (PChoice p q)
    (at level 60, right associativity).

  (* ── Punctuation aliases ──────────────────────────────────────── *)
  Definition LEFT_BRACE  : pat := sym "{".
  Definition RIGHT_BRACE : pat := sym "}".
  Definition LEFT_BRACKET  : pat := sym "[".
  Definition RIGHT_BRACKET : pat := sym "]".
  Definition LPAREN : pat := sym "(".
  Definition RPAREN : pat := sym ")".
  Definition COMMA  : pat := sym ",".
  Definition SEMI   : pat := sym ";".
  Definition COLON  : pat := sym ":".
  Definition DOT    : pat := sym ".".
  Definition ARROW  : pat := sym "=>".
  Definition BANG   : pat := sym "!".
  Definition ASSIGN : pat := sym "=".
  Definition PLUS_ASSIGN  : pat := sym "+=".
  Definition MINUS_ASSIGN : pat := sym "-=".
  Definition LESS_THAN    : pat := sym "<".

  (* ══════════════════════════════════════════════════════════════════
     Lexical rules
     ══════════════════════════════════════════════════════════════════ *)

  (* ── String literals ──────────────────────────────────────────── *)
  (* quasi-jessie.js.ts: stringLitSngl <- SQUOTE ... SQUOTE;
     No escape handling in this subset. *)
  Definition string_lit_single : pat :=
    sym "'" >> star (PNot (sym "'") >> PSet fullcharset) >> sym "'".

  Definition string_lit : pat := tok string_lit_single.

  (* ══════════════════════════════════════════════════════════════════
     Expressions
     ══════════════════════════════════════════════════════════════════ *)

  (* ── L-value ──────────────────────────────────────────────────── *)
  (* quasi-jessie.js.ts: lValue <- ... ; narrowed to identifiers only. *)
  Definition lvalue : pat := ident.

  (* quasi-jessie.js.ts: opAssign <- lValue OP_ASSIGN assignExpr *)
  Definition op_assign : pat :=
    lvalue >> (PLUS_ASSIGN /// MINUS_ASSIGN) >> PNT 0.

  (* quasi-jessie.js.ts: assignExpr <- lValue EQ assignExpr *)
  Definition assign_expr : pat :=
    lvalue >> ASSIGN >> PNT 0.

  Definition paren_expr : pat :=
    LPAREN >> PNT 0 >> RPAREN.

  (* ── Record / object literal ──────────────────────────────────── *)
  (* quasi-jessie.js.ts: record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE *)
  Definition record : pat :=
    LEFT_BRACE >> opt (PNT 2 >> star (COMMA >> PNT 2) >> opt COMMA) >> RIGHT_BRACE.

  (* ── Array literal ────────────────────────────────────────────── *)
  Definition comma_list (elem : pat) : pat :=
    elem >> star (COMMA >> elem).

  Definition array_pat : pat :=
    LEFT_BRACKET >> opt (comma_list (PNT 0) >> opt COMMA) >> RIGHT_BRACKET.

  (* ── Arrow function ───────────────────────────────────────────── *)
  Definition match_array_param : pat :=
    LEFT_BRACKET >> opt (comma_list ident) >> RIGHT_BRACKET.

  Definition arrow_param : pat := match_array_param /// ident.

  Definition arrow_params : pat :=
    ident /// (LPAREN >> opt (comma_list arrow_param) >> RPAREN).

  Definition arrow_body : pat :=
    PNT 4 /// paren_expr /// PNT 0.

  (* quasi-jessie.js.ts:
     arrowFunc <- arrowParams _NO_NEWLINE ARROW block
                / arrowParams _NO_NEWLINE ARROW assignExpr; *)
  Definition arrow_func : pat :=
    arrow_params >> ARROW >> arrow_body.

  (* ── Postfix operations ───────────────────────────────────────── *)
  (* quasi-jessie.js.ts:
     memberPostOp / callPostOp extensions inherited from Justin. *)
  Definition expr_post_op : pat := QuasiJustin.post_op 0.

  (* ── Comparison ───────────────────────────────────────────────── *)
  Definition less_than : pat :=
    PNT 1 >> star expr_post_op >> LESS_THAN
         >> PNT 1 >> star expr_post_op.

  (* ══════════════════════════════════════════════════════════════════
     Declarations
     ══════════════════════════════════════════════════════════════════ *)

  Definition const_decl : pat :=
    kw "const" >> ident >> ASSIGN >> PNT 0 >> SEMI.

  Definition let_decl : pat :=
    kw "let" >> ident >> opt (ASSIGN >> PNT 0) >> SEMI.

  (* quasi-jessie.js.ts: importDeclaration *)
  Definition import_stmt : pat :=
    kw "import" >> LEFT_BRACE >> ident >> RIGHT_BRACE
                >> kw "from" >> string_lit >> SEMI.

  (* ══════════════════════════════════════════════════════════════════
     Statements
     ══════════════════════════════════════════════════════════════════ *)

  (* quasi-jessie.js.ts: returnStatement production subset. *)
  Definition return_stmt : pat :=
    kw "return" >> PNT 0 >> SEMI.

  Definition throw_stmt : pat :=
    kw "throw" >> PNT 0 >> SEMI.

  (* quasi-jessie.js.ts: ifStatement *)
  Definition if_stmt : pat :=
    kw "if" >> LPAREN >> PNT 0 >> RPAREN
         >> PNT 4
         >> opt (kw "else" >> PNT 4).

  (* quasi-jessie.js.ts: exprStatement <- ~cantStartExprStatement expr SEMI. *)
  Definition expr_stmt : pat := PNT 0 >> SEMI.

  Definition assert_stmt : pat :=
    kw "assert" >> LPAREN >> PNT 0 >> RPAREN >> SEMI.

  (* quasi-jessie.js.ts: block production subset. *)
  Definition block : pat :=
    LEFT_BRACE >> star (PNT 3) >> RIGHT_BRACE.

  (* ══════════════════════════════════════════════════════════════════
     Grammar (indexed productions, referenced by PNT n)
     ══════════════════════════════════════════════════════════════════ *)
  Definition grammar : Syntax.grammar :=
    [ (* 0 expr — quasi-jessie.js.ts: assignExpr production subset *)
      arrow_func
      /// op_assign
      /// assign_expr
      /// less_than
      /// (BANG >> PNT 0)
      /// (PNT 1 >> star expr_post_op);
      (* 1 primaryExpr — quasi-jessie.js.ts: primaryExpr inherits Justin *)
      string_lit
      /// number
      /// array_pat
      /// record
      /// paren_expr
      /// ident;
      (* 2 propDef *)
      (ident /// number) >> COLON >> PNT 0;
      (* 3 statement — quasi-jessie.js.ts: binding/import/if/throw/exprStatement/declOp *)
      if_stmt
      /// import_stmt
      /// throw_stmt
      /// const_decl
      /// let_decl
      /// return_stmt
      /// assert_stmt
      /// expr_stmt;
      (* 4 block / arrow body block *)
      block;
      (* 5 module body — quasi-jessie.js.ts: start production subset *)
      ws >> star (PNT 3) >> ws >> eof
    ].

  Definition expr : pat := PNT 0.
  Definition statement : pat := PNT 3.
  Definition moduleBody : pat := PNT 5.
  Definition exact_module_source (src : string) : pat :=
    ws >> string_pat src >> ws >> eof.

End JessieGrammar.
