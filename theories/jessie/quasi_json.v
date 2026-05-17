From Coq Require Import Lists.List Strings.Ascii Strings.String.
From Peg Require Import Charset Syntax Match.

Import ListNotations.
Open Scope string_scope.

Module QuasiJson.
  (* These token patterns come from quasi-json.js.ts. *)

  Section CharacterPatterns.
  Definition char_pat (c : ascii) : pat :=
    PSet (fun a => Ascii.eqb a c).

  Definition charset_pat (cs : charset) : pat := PSet cs.

  Fixpoint string_pat (s : string) : pat :=
    match s with
    | EmptyString => PEmpty
    | String c s' => PSequence (char_pat c) (string_pat s')
    end.
  End CharacterPatterns.

  Section Combinators.
  Definition seq (p q : pat) : pat := PSequence p q.
  Definition alt (p q : pat) : pat := PChoice p q.
  Definition opt (p : pat) : pat := PChoice p PEmpty.
  Definition star (p : pat) : pat := PRepetition p.
  Definition plus (p : pat) : pat := PSequence p (PRepetition p).
  End Combinators.

  Section AsciiHelpers.
  Definition ascii_between (lo hi : nat) (a : ascii) : bool :=
    let n := nat_of_ascii a in
    (Nat.leb lo n) && (Nat.leb n hi).

  Definition one_of (xs : list ascii) : charset :=
    fun a => existsb (fun x => Ascii.eqb x a) xs.
  End AsciiHelpers.

  Section Whitespace.
  Definition ws_char : pat :=
    charset_pat (one_of [" "%char; "009"%char; "010"%char; "013"%char]).

  Definition line_comment : pat :=
    seq (string_pat "//")
      (star (seq (PNot (char_pat "010"%char)) (PSet fullcharset))).

  (* quasi-json.js.ts: _WS <- [\t\n\r ]* ${_ => SKIP}; *)
  Definition ws : pat := star (alt ws_char line_comment).

  Definition tok (p : pat) : pat := seq p ws.

  Definition kw (s : string) : pat := tok (string_pat s).

  Definition sym (s : string) : pat := tok (string_pat s).
  End Whitespace.

  Section Numbers.
  (* quasi-json.js.ts: digit <- [0-9]; *)
  Definition digit : pat :=
    charset_pat (ascii_between 48 57).

  Definition nonzero_digit : pat :=
    charset_pat (ascii_between 49 57).

  Definition unsigned_int : pat :=
    alt digit (seq nonzero_digit (star digit)).

  (* quasi-json.js.ts: int production subset. *)
  Definition number_core : pat :=
    alt unsigned_int (seq (char_pat "-"%char) unsigned_int).

  (* quasi-json.js.ts: NUMBER production subset. *)
  Definition number : pat := tok number_core.
  End Numbers.

  Section EOF.
  (* quasi-json.js.ts: _EOF <- ~.; *)
  Definition eof : pat := PNot (charset_pat fullcharset).
  End EOF.

  Section StringLiteral.
  (* quasi-json.js.ts: STRING <- ... double-quoted string. *)
  Definition string_lit_double_core : pat :=
    seq (sym "\"")
      (seq (star (seq (PNot (sym "\"")) (PSet fullcharset)))
           (sym "\"")).

  Definition STRING : pat := tok string_lit_double_core.
  End StringLiteral.

  Section PunctuationAliases.
  (* These token patterns come from quasi-json.js.ts. *)
  Definition LEFT_BRACE  : pat := sym "{".
  Definition RIGHT_BRACE : pat := sym "}".
  Definition LEFT_BRACKET  : pat := sym "[".
  Definition RIGHT_BRACKET : pat := sym "]".
  Definition COMMA  : pat := sym ",".
  Definition COLON  : pat := sym ":".
  End PunctuationAliases.

  Section Examples.
  Example parse_number_0 :
    matches_comp [] number "0" 64 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_number_1_before_rparen :
    matches_comp [] number "1)" 64 = Some (Success ")").
  Proof. vm_compute. reflexivity. Qed.
  End Examples.
End QuasiJson.
