(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.proofmode Require Import tactics.

Section wp.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ}.
Implicit Types p : pbit.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Hint Resolve head_prim_reducible head_reducible_prim_step.

Lemma wp_ectx_bind {p E e} K Φ :
  WP e @ p; E {{ v, WP fill K (of_val v) @ p; E {{ Φ }} }} ⊢ WP fill K e @ p; E {{ Φ }}.
Proof. apply: weakestpre.wp_bind. Qed.

Lemma wp_lift_head p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (Hv) "H". iApply wp_lift_step=>//. iIntros (σ1) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct p; eauto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_head_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (? Hsafe Hpure) "H"; iApply wp_lift_pure_step; eauto.
  by destruct p; eauto. by iNext; iIntros (????); iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct p; eauto.
  by iNext; iIntros (e2 σ2 efs ?); iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" $! v2 σ2 efs with "[#]") as "(% & $ & $)"=>//; subst.
  by iApply big_sepL_nil.
Qed.

Lemma wp_lift_pure_det_head_step {p E Φ} e1 e2 efs :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  ▷ (WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (???) "H"; iApply wp_lift_pure_det_step; eauto.
  by destruct p; eauto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork {p E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ p; E {{ Φ }} ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) ?big_sepL_nil ?right_id; eauto.
  by destruct p; eauto.
Qed.
End wp.
