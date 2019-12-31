From iris.algebra Require Import auth.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import auth.
From iris.program_logic Require Export adequacy.
From iris.heap_lang Require addenda.
From iris.heap_lang Require Export heap robust_safety.
From iris.proofmode Require Import tactics.
Import addenda.ownp.

Theorem heap_adequacy Σ `{heapPreG Σ} p e h φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e @ p; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate p e (good_state h) φ.
Proof.
  intros Hwp. apply (ownP_adequacy _ _ _ _). iIntros (?) "Hσ".
  iMod (heap_ctx_alloc with "Hσ") as (γ) "Hh".
  by iApply (Hwp (HeapG _ _ _ _ γ) with "Hh").
Qed.

Theorem adequacy_safety Σ `{heapPreG Σ} p e h1 t2 σ2 :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e @ p; ⊤ {{ v, True }}) →
  rtc step ([e], good_state h1) (t2, σ2) → is_good σ2.
Proof.
  intros Hwp Hsteps.
  apply: (ownP_invariance  _ p _ _ _ _ is_good) Hsteps=> /= ?.
  iIntros "Hσ". iMod (heap_ctx_alloc with "Hσ") as (γ) "#Hh".
  set G := (HeapG _  _ _ _ γ). iModIntro. iSplitL.
  by iApply (Hwp G). by iApply (@heap_ctx_is_good _ G).
Qed.

Theorem robust_safety_strong Σ `{heapPreG Σ} c es t2 σ2 :
  AdvCtx c → (∀ `{heapG Σ}, True ⊢ [∗ list] e ∈ es, verified_code e) →
  rtc step ([ctx_plug c es], good_state ∅) (t2, σ2) → is_good σ2.
Proof.
  move=>Hadv Hcode Hsteps. apply: (adequacy_safety Σ noprogress) Hsteps=>?.
  iIntros "Hh". iApply (wp_wand _ _ _ low with "[-] []"); last by iIntros.
  iApply (robust_safetyI with "Hh [] []").
  by iApply adv_ctx_intro. by iApply Hcode.
Qed.

(* Compatibility: [ctx_fill] plugs a single expression into a context. *)
Definition ctx_fill (c : ctx) (e : expr) : expr := ctx_plug c [e].

Corollary robust_safety Σ `{heapPreG Σ} c p e t2 σ2 :
  AdvCtx c → is_closed [] e →
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e @ p; ⊤ {{ low }}) →
  rtc step ([ctx_fill c e], good_state ∅) (t2, σ2) → is_good σ2.
Proof.
  move=>?? Hwp Hsteps. apply: robust_safety_strong; eauto.
  move=>hG. rewrite big_opL_cons big_opL_nil right_id.
  iExists p. iIntros "!#". iSplit. done. by iApply Hwp.
Qed.
