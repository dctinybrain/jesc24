From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Definition assume : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assume:' e" := (assume (λ: <>, e))%E (at level 99) : expr_scope.

Lemma wp_assume `{heapG Σ} E e (Φ : val → iProp Σ) :
  WP e @ E ?{{ v, ⌜v = LitV (LitBool true)⌝ -∗ ▷ Φ (LitV LitUnit) }} -∗
  WP assume: e @ E ?{{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /assume. wp_bind (Rec _ _ _).
  case: (decide (Closed [] e)) => ?; last by iApply wp_stuck_rec_open.
  wp_value. wp_let. wp_seq. iApply (wp_wand with "HΦ").
  iIntros (v) "Hret". case: (decide (is_lit_bool v))=>Hb; last
    by iApply wp_stuck_if; auto using to_of_val.
  case: Hb=>[] b Hb. have {Hb}->: v = #b by apply (inj of_val); rewrite -Hb.
  case: b.
  - iSpecialize ("Hret" with "[]"); first done. by wp_if.
  - iClear "Hret". wp_if. iApply wp_stuck_app_nrec.
    done. done. by move=>[] ? [] ? [] ?.
Qed.
