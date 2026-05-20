From Peg Require Import Charset Syntax Match.
From iris.jessie Require Import quasi_json.

Module JessiePegNotation.
  Import QuasiJson.
  Notation "p >> q" := (PSequence p q)
    (at level 69, right associativity).
  Notation "p /// q" := (PChoice p q)
    (at level 60, right associativity).
  Notation "p ?" := (PChoice p PEmpty)
    (at level 68).
  Notation "p `sepBy` sep" := (p >> star (sep >> p))
    (at level 60, right associativity).
End JessiePegNotation.
