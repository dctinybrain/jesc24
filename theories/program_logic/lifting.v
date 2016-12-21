From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export big_op.
From iris.proofmode Require Import tactics.

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types p : pbit.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if p then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite wp_unfold /wp_pre. by auto.
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ, state_interp σ ={E,∅}=∗ ⌜¬ language.progress e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (?) "H"; rewrite wp_unfold /wp_pre; iRight; iSplit; first done.
  iIntros (σ) "Hσ"; iMod ("H" $! _ with "Hσ") as "#H"; iDestruct "H" as % Hstuck.
  iModIntro; iSplit; first done; iNext; iIntros (e' σ' efs Hstep); exfalso.
  by apply Hstuck; right; exists e', σ', efs.
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_pure_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, if p then reducible e1 σ1 else True) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (? Hsafe Hstep) "H". iApply wp_lift_step; first done.
  iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro. iSplit; first by iPureIntro; apply Hsafe.
  iNext; iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose"; iModIntro. iFrame "Hσ". iApply "H"; auto.
Qed.

Lemma wp_lift_pure_stuck `{Inhabited (state Λ)} E Φ e :
  (∀ σ, ¬ language.progress e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck); iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    by exfalso; apply (Hstuck inhabitant); left; exists v.
  - iIntros (σ) "_"; iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
    by iModIntro; iPureIntro; apply Hstuck.
Qed.

Lemma wp_lift_atomic_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if p then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step p E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro; iNext; iIntros (e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step {p E Φ} e1 e2 efs :
  to_val e1 = None →
  (∀ σ1, if p then reducible e1 σ1 else true) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  ▷ (WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?? Hpuredet) "?". iApply (wp_lift_pure_step p E); try done.
  by intros; eapply Hpuredet. iNext. by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.
End lifting.
