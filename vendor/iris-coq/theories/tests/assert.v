From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import notation.
From iris.heap_lang.lib Require Import assume.
From iris.heap_lang Require Import proofmode.
Import uPred.

(** * Hoare triples for assertions and assumptions *)

Section ht.
  Context `{heapG Σ}.
  Implicit Types Φ : val → iProp Σ.

  Lemma ht_assert p E e P Φ :
    {{ P }} e @ p; E {{ v, ⌜v = #true⌝ ∗ ▷ Φ ()%V }} ⊢
    {{ P }} assert: e @ p; E {{ Φ }}.
  Proof.
    iIntros "#He !# Hp". wp_apply wp_assert.
    setoid_rewrite <- always_pure.
    setoid_rewrite always_and_sep_l'.
    by iApply ("He" with "Hp").
  Qed.

  Lemma ht_assume e E P Φ :
    {{ P }} e @ E ?{{ v, ⌜v = #true⌝ -∗ ▷ Φ ()%V }} ⊢
    {{ P }} assume: e @ E ?{{ Φ }}.
  Proof.
    iIntros "#He !# Hp". wp_apply wp_assume.
    by iApply ("He" with "Hp").
  Qed.
End ht.
