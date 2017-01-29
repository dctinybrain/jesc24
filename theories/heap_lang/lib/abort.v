From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

(* Notation because solve_closed won't unfold definitions. *)
Notation abort := (#0 #0)%E (only parsing).

Lemma wp_abort `{heapG Σ} E (Φ : val → iProp Σ) :
  WP abort @ E ?{{ Φ }}%I.
Proof.
  iApply wp_stuck_app_nrec. done. done. by move=>[] ? [] ? [] ?.
Qed.
