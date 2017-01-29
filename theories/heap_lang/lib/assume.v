From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang.lib Require Import abort.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Definition assume : val := λ: "v", if: "v" #() then #() else abort.
(* just below ;; *)
Notation "'assume:' e" := (assume (λ: <>, e))%E (at level 99) : expr_scope.

Lemma wp_assume `{heapG Σ} E e (Φ : val → iProp Σ) :
  WP e @ E ?{{ v, ⌜v = LitV (LitBool true)⌝ -∗ ▷ Φ (LitV LitUnit) }} -∗
  WP assume: e @ E ?{{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /assume. wp_bind (Rec _ _ _).
  case: (decide (Closed [] e)) => ?; last by iApply wp_stuck_rec_open.
  wp_value. wp_let. wp_seq. iApply (wp_wand with "HΦ").
  iIntros (v) "Hret". case: (decide (is_bool v))=>Hb;
    last by iApply wp_stuck_if; auto using to_of_val.
  destruct Hb as (b&Hb). have {Hb}->: v = LitV (LitBool b)
    by move: Hb; case: v => // -[] // ? [] ?; subst.
  case: b.
  - iSpecialize ("Hret" with "[]"); first done. by wp_if.
  - iClear "Hret". wp_if. by iApply wp_abort.
Qed.
