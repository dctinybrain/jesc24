From Peg Require Import Charset Syntax Match.

Module JessiePegNotation.
  Notation "p >> q" := (PSequence p q)
    (at level 69, right associativity).
  Notation "p /// q" := (PChoice p q)
    (at level 60, right associativity).
  Notation "p ?" := (PChoice p PEmpty)
    (at level 68).
  Notation "p `sepBy` sep" := (p >> star (sep >> p))
    (at level 60, right associativity).
End JessiePegNotation.
