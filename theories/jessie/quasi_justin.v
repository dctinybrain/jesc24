From Coq Require Import Bool Lists.List Strings.Ascii Strings.String.
From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import quasi_json.

Import ListNotations.
Open Scope string_scope.

Module QuasiJustin.
  Import QuasiJson.

  (* Experimental peg-coq expression/recognizer layer, parallel to
     quasi-justin, but limited to the fragments used by the current Jessie
     makeCounter examples. This file defines PEG patterns and executable
     recognition tests over the vendored peg-coq slice under
     vendor/peg-coq/theories, imported here through the upstream-style Peg
     namespace, not AST construction. *)

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

  (* ── String literals ──────────────────────────────────────────── *)
  (* quasi-justin.js.ts:
     STRING <- super.STRING
            / "'" < (~"'" character)* > "'" _WS  ${s => transformSingleQuote(s)};
     No double-quoted string literals (super.STRING from JSON) in this
     simplified subset; only single-quoted strings are defined here. *)
  Definition string_lit_single : pat :=
    seq (sym "'") (seq (star (seq (PNot (sym "'")) (PSet fullcharset))) (sym "'")).

  Definition string_lit : pat := tok string_lit_single.

  (* ── Punctuation aliases ──────────────────────────────────────── *)
  (* DOT comes from quasi-justin.js.ts (memberPostOp uses DOT). *)
  Definition DOT : pat := sym ".".

  (* quasi-justin.js.ts:
     memberPostOp <- LEFT_BRACKET indexExpr RIGHT_BRACKET / DOT IDENT_NAME / quasiExpr
     callPostOp <- memberPostOp / args
  *)
  Definition post_op (expr_nt : nat) : pat :=
    alt
      (seq DOT ident)
      (seq (sym "(")
        (seq
          (opt (seq (PNT expr_nt) (star (seq (sym ",") (PNT expr_nt)))))
          (sym ")"))).

  (* quasi-justin.js.ts:
     record <- LEFT_BRACE propDef ** _COMMA _COMMA? RIGHT_BRACE
  *)
  Definition object_pat (expr_nt propdef_nt : nat) : pat :=
    seq (sym "{")
      (seq
        (opt
          (seq (PNT propdef_nt)
            (seq (star (seq (sym ",") (PNT propdef_nt)))
              (opt (sym ",")))))
        (sym "}")).

  Definition grammar : grammar :=
    [ (* 0 *) (* quasi-justin.js.ts: callExpr production subset. *)
      seq (PNT 1) (star (post_op 0));
      (* 1 *) (* quasi-justin.js.ts: primaryExpr production subset. *)
      alt number
                (alt (object_pat 0 2)
                  (alt (seq (sym "(") (seq (PNT 0) (sym ")")))
                       ident));
      (* 2 *) (* quasi-justin.js.ts: propDef production subset. *)
      seq (alt ident number) (seq (sym ":") (PNT 0))
    ].

  Definition expr : pat := PNT 0.
  Definition primaryExpr : pat := PNT 1.
  Definition propDef : pat := PNT 2.

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
End QuasiJustin.
