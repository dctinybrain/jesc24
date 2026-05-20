From Coq Require Import Bool Lists.List Strings.Ascii Strings.String.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import peg_notation quasi_json.

Import ListNotations.
Open Scope string_scope.

Module QuasiJustin.
  Import JessiePegNotation.
  Import QuasiJson.

  (* These patterns come from quasi-justin.js.ts. *)

  Section Identifiers.
  Definition ident_start : pat :=
    charset_pat (fun a =>
      orb (ascii_between 65 90 a)
        (orb (ascii_between 97 122 a)
          (Ascii.eqb a "_"%char))).

  Definition ident_continue : pat :=
    charset_pat (fun a =>
      orb (ascii_between 65 90 a)
        (orb (ascii_between 97 122 a)
          (orb (ascii_between 48 57 a)
            (Ascii.eqb a "_"%char)))).

  Definition ident_core : pat := seq ident_start (star ident_continue).

  (* quasi-justin.js.ts: useVar <- IDENT ${id => ['use', id]}; *)
  Definition ident : pat := tok ident_core.
  End Identifiers.

  Section StringLiterals.
  (* quasi-justin.js.ts:
     STRING <- super.STRING
            / "'" < (~"'" character)* > "'" _WS  ${s => transformSingleQuote(s)};
     super.STRING from QuasiJson handles double-quoted strings. *)
  Definition string_lit_single : pat :=
    seq (sym "'") (seq (star (seq (PNot (sym "'")) (PSet fullcharset))) (sym "'")).

  Definition string_lit : pat := QuasiJson.STRING /// tok string_lit_single.
  End StringLiterals.

  Section PunctuationAliases.
  (* DOT, LEFT_PAREN, RIGHT_PAREN come from quasi-justin.js.ts
     (memberPostOp / callPostOp use DOT; arrowParams uses parens). *)
  Definition DOT : pat := sym ".".
  Definition LPAREN : pat := sym "(".
  Definition RPAREN : pat := sym ")".
  End PunctuationAliases.

  Section PostOperations.
  (* quasi-justin.js.ts:
     memberPostOp <- LEFT_BRACKET indexExpr RIGHT_BRACKET / DOT IDENT_NAME / quasiExpr
     callPostOp <- memberPostOp / args
  *)
  Definition post_op (expr_nt : nat) : pat :=
    (DOT >> ident) ///
    (sym "(" >> ((PNT expr_nt) `sepBy` sym ",")? >> sym ")").

  (* quasi-justin.js.ts:
     record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE
  *)
  Definition object_pat (expr_nt propdef_nt : nat) : pat :=
    sym "{" >> ((PNT propdef_nt) `sepBy` sym "," >> (sym ",")?)? >> sym "}".
  End PostOperations.

  Section Grammar.
  Definition grammar : grammar :=
    [ PNT 1 >> star (post_op 0);
      number /// object_pat 0 2 /// (sym "(" >> PNT 0 >> sym ")") /// ident;
      (ident /// number) >> sym ":" >> PNT 0
    ].

  Definition expr : pat := PNT 0.
  Definition primaryExpr : pat := PNT 1.
  Definition propDef : pat := PNT 2.
  End Grammar.

  Section Examples.
  Example parse_use_var :
    matches_comp grammar expr "count" 128 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_member_expr :
    matches_comp grammar expr "c.incr" 128 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_call_expr :
    matches_comp grammar expr "makeCounter()" 256 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_record_expr :
    matches_comp grammar expr "{ incr: c.incr }" 512 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.
  End Examples.
End QuasiJustin.
