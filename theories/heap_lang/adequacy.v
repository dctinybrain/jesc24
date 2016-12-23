From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import auth.
From iris.program_logic Require Export adequacy.
From iris.heap_lang Require Export heap.
From iris.heap_lang Require Import addenda robust_safety.
From iris.proofmode Require Import tactics.
Import addenda.ownp.

Theorem heap_adequacy Σ `{heapPreG Σ} p e h φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e @ p; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate p e (good_state h) φ.
Proof.
  intros Hwp. apply (ownP_adequacy _ _ _ _). iIntros (?) "Hσ".
  iMod (heap_ctx_alloc with "Hσ") as (γ) "#Hh".
  by iApply (Hwp (HeapG _ _ _ γ) with "Hh").
Qed.

Theorem heap_safety Σ `{heapPreG Σ} p e h1 t2 σ2 :
  (∀ `{heapG Σ}, ∃ Φ, heap_ctx -∗ WP e @ p; ⊤ {{ Φ }}) →
  rtc step ([e], good_state h1) (t2, σ2) → is_good σ2.
Proof.
  intros Hwp Hsteps.
  apply: (ownP_invariance  _ p _ _ _ _ is_good) Hsteps=> /= ?.
  iIntros "Hσ". iMod (heap_ctx_alloc with "Hσ") as (γ) "#Hh".
  set G := (HeapG _  _ _ γ). iModIntro. iSplitL.
  - case: (Hwp G) => Φ Hwp'. iExists Φ. by iApply Hwp'.
  - by iApply (@heap_ctx_is_good _ G with "Hh").
Qed.

Corollary robust_safety Σ `{heapPreG Σ} C p e t2 σ2 :
  adv_ctx C → is_closed [] e →
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e @ p; ⊤ {{ low }}) →
  rtc step ([ctx_fill C e], good_state ∅) (t2, σ2) → is_good σ2.
Proof.
  move=>?? Hwp Hsteps. apply: (heap_safety Σ) Hsteps=>?.
  exists low. iIntros "#Hh". rewrite (substitute_empty (ctx_fill _ _)).
  iApply (robust_safety' with "[$Hh] [] [] []").
  - by iApply adv_ctx_low.
  - by rewrite low_env_empty.
  - iAlways. iSplit. done. by iApply Hwp.
Qed.
