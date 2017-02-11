From iris.heap_lang Require Export heap.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Import tactics.
Import uPred.

Local Hint Resolve to_of_val.

(** * Eliminating lifted/low values *)
(**
  These lemmas are useful at the boundary between verified and
  adversarial code.
*)
Section wp_on_val.
  Context `{heapG Σ} (Ψ : loc → iProp Σ).
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Use [wp_stuck_var] for variables. *)

  (** Use [on_val_elim] or [on_val_rec] for functions. *)

  Lemma wp_on_val_app e1 e2 :
    WP e1 ?{{ on_val Ψ }} -∗
    WP e2 ?{{ on_val Ψ }} -∗
    WP App e1 e2 ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_bind e1. iApply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_bind e2. iApply (wp_wand with "He2"). iIntros (v2) "Hv2".
    case: (decide (is_rec (of_val v1)))=>Hrec;
      last by iApply wp_stuck_app_nrec.
    destruct (is_rec_val _ Hrec) as (f&x&e&?&->).
    rewrite on_val_rec always_elim.
    iApply wp_rec; [done|by exists v2|]. iNext.
    iApply ("Hv1" with "[$Hv2]"). by iIntros.
  Qed.

  Lemma wp_on_val_lit p E lit :
    on_lit Ψ lit -∗
    WP (Lit lit) @ p; E {{ on_val Ψ }}.
  Proof. iIntros "Hlit". wp_value. by simpl_on_val. Qed.

  Hint Extern 1 (_ -∗ on_val Ψ (LitV ?lit)) =>
    rewrite (on_val_elim Ψ (LitV lit)) on_lit_elim.
  Hint Extern 1 (on_val Ψ (InjLV ?v) -∗ on_val Ψ (InjRV ?v)) =>
    rewrite (on_val_elim Ψ (InjLV v)) (on_val_elim Ψ (InjRV v)).
  Hint Extern 2 (_ -∗ on_val Ψ (InjLV ?v)) =>
    rewrite (on_val_elim Ψ (InjLV v)) -later_intro.
  Hint Extern 2 (_ -∗ on_val Ψ (InjRV ?v)) =>
    rewrite (on_val_elim Ψ (InjRV v)) -later_intro.

  Lemma on_val_un_op_eval op v1 v2 :
    un_op_eval op v1 = Some v2 →
    on_val Ψ v1 -∗ on_val Ψ v2.
  Proof.
    case: op; destruct v1 as [|lit| | |];
    repeat (discriminate 1 || injection 1 as <- || destruct lit); auto.
  Qed.

  Lemma wp_on_val_un_op E op e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP UnOp op e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    case EV: (un_op_eval op v)=>[v'|]; last by iApply wp_stuck_un_op.
    iApply wp_un_op; eauto. iNext.
    by iApply (on_val_un_op_eval with "Hv").
  Qed.

  Lemma on_val_bin_op_eval op v1 v2 v3 :
    bin_op_eval op v1 v2 = Some v3 →
    on_val Ψ v1 ∗ on_val Ψ v2 -∗ on_val Ψ v3.
  Proof.
    case: op; destruct v1 as [|lit1| | |]; destruct v2 as [|lit2| | |];
    repeat (discriminate 1 || injection 1 as <- || destruct lit1
      || destruct lit2); auto.
  Qed.

  Lemma wp_on_val_bin_op E op e1 e2 :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    WP BinOp op e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_bind e1. iApply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_bind e2. iApply (wp_wand with "He2"). iIntros (v2) "Hv2".
    case EV: (bin_op_eval op v1 v2)=>[v'|]; last by iApply wp_stuck_bin_op.
    iApply wp_bin_op; eauto. iNext.
    by iApply (on_val_bin_op_eval with "[$Hv1 $Hv2]").
  Qed.

  (* Misnamed. *)
  Lemma wp_on_val_if E e0 e1 e2 Φ0 Φ :
    WP e0 @ E ?{{ Φ0 }} -∗
    ▷ (WP e1 @ E ?{{ Φ }} ∧ WP e2 @ E ?{{ Φ }}) -∗
    WP If e0 e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He0 Hei".
    wp_bind e0. iApply (wp_wand with "He0"). iIntros (v) "Hv".
    case: (decide (is_bool (of_val v)))=>Hbool; last by iApply wp_stuck_if.
    case: Hbool=>-[]->.
    - iApply wp_if_true. iNext. by iDestruct "Hei" as "[? _]".
    - iApply wp_if_false. iNext. by iDestruct "Hei" as "[_ ?]".
  Qed.

  Lemma wp_on_val_pair E e1 e2 :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    WP Pair e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_bind e1. iApply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_bind e2. iApply (wp_wand with "He2"). iIntros (v2) "Hv2".
    wp_value. simpl_on_val. by iFrame.
  Qed.

  Lemma wp_on_val_fst E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP Fst e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    case: (decide (is_pair (of_val v)))=>Hp; last by iApply wp_stuck_fst.
    destruct (is_pair_val _ Hp) as (v1&v2&->).
    iApply wp_fst; [done|by exists v2|]. iNext.
    by iDestruct "Hv" as "(Hv1&_)".
  Qed.

  Lemma wp_on_val_snd E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP Snd e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    case: (decide (is_pair (of_val v)))=>Hp; last by iApply wp_stuck_snd.
    destruct (is_pair_val _ Hp) as (v1&v2&->).
    iApply wp_snd; [by exists v1|done|]. iNext.
    by iDestruct "Hv" as "(_&Hv2)".
  Qed.

  Lemma wp_on_val_inl E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP InjL e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    wp_value. simpl_on_val. by iNext.
  Qed.

  Lemma wp_on_val_inr E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP InjR e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    wp_value. simpl_on_val. by iNext.
  Qed.

  Lemma wp_on_val_case E e0 e1 e2 Φ :
    WP e0 @ E ?{{ on_val Ψ }} -∗
    ▷ (∀ v0, on_val Ψ v0 -∗
      WP App e1 (of_val v0) @ E ?{{ Φ }} ∧
      WP App e2 (of_val v0) @ E ?{{ Φ }}) -∗
    WP Case e0 e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He0 Hk".
    wp_bind e0. iApply (wp_wand with "He0"). iIntros (v) "Hv".
    case: (decide (is_inl (of_val v) ∨ is_inr (of_val v)))=>Hc;
      last by iApply wp_stuck_case.
    case: Hc=>[Hinl | Hinr].
    - destruct (is_inl_val _ Hinl) as (v0&->).
      iApply wp_case_inl; first by exists v0. iNext.
      setoid_rewrite and_elim_l. by iApply ("Hk" with "[$Hv]").
    - destruct (is_inr_val _ Hinr) as (v0&->).
      iApply wp_case_inr; first by exists v0. iNext.
      setoid_rewrite and_elim_r. by iApply ("Hk" with "[$Hv]").
  Qed.

  (** We don't need compatibility for [Assert e]. *)

  Lemma wp_on_val_fork p E e Φ1 :
    WP e @ p; ⊤ {{ Φ1 }} -∗
    WP Fork e @ p; E {{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply wp_fork. iSplitR "He"; first by simpl_on_val.
    iApply (wp_wand with "He"). by iIntros.
  Qed.

  (** The heap may be inspected or modified according to [Ψ]. *)

  Lemma wp_on_val_alloc p E e Φ :
    WP e @ p; E {{ Φ }} -∗
    (∀ v, Φ v -∗ WP Alloc (of_val v) @ p; E {{ on_val Ψ }}) -∗
    WP Alloc e @ p; E {{ on_val Ψ }}.
  Proof.
    iIntros "He Halloc".
    wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply ("Halloc" with "Hv").
  Qed.

  Lemma wp_on_val_load E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    (∀ l, Ψ l -∗ WP Load (Lit (LitLoc l)) @ E ?{{ on_val Ψ }}) -∗
    WP Load e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He Hload".
    wp_bind e. iApply (wp_wand with "He"). iIntros (v) "Hv".
    case: (decide (is_loc (of_val v)))=>Hl; last by iApply wp_stuck_load.
    destruct (is_loc_val _ Hl) as (l&->). rewrite on_val_elim on_lit_elim.
    by iApply ("Hload" with "Hv").
  Qed.

  Lemma wp_on_val_store E e1 e2 :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    (∀ l1 v2, Ψ l1 -∗ on_val Ψ v2 -∗
     WP Store (Lit (LitLoc l1)) (of_val v2) @ E ?{{ on_val Ψ }}) -∗
    WP Store e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2 Hstore".
    wp_bind e1. iApply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_bind e2. iApply (wp_wand with "He2"). iIntros (v2) "Hv2".
    case: (decide (is_loc (of_val v1)))=>Hl; last by iApply wp_stuck_store.
    destruct (is_loc_val _ Hl) as (l1&->). rewrite on_val_elim on_lit_elim.
    by iApply ("Hstore" with "Hv1 Hv2").
  Qed.

  Lemma wp_on_val_cas E e0 e1 e2 Φ1 :
    WP e0 @ E ?{{ on_val Ψ }} -∗
    WP e1 @ E ?{{ Φ1 }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    (∀ l0 v1 v2, Ψ l0 -∗ on_val Ψ v2 -∗
     WP CAS (Lit (LitLoc l0)) (of_val v1) (of_val v2) @ E ?{{ on_val Ψ }}) -∗
    WP CAS e0 e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He0 He1 He2 Hcas".
    wp_bind e0. iApply (wp_wand with "He0"). iIntros (v0) "Hv0".
    wp_bind e1. iApply (wp_wand with "He1"). iIntros (v1) "_".
    wp_bind e2. iApply (wp_wand with "He2"). iIntros (v2) "Hv2".
    case: (decide (is_loc (of_val v0)))=>Hl; last by iApply wp_stuck_cas.
    destruct (is_loc_val _ Hl) as (l0&->). rewrite on_val_elim on_lit_elim.
    by iApply ("Hcas" with "Hv0 Hv2").
  Qed.
End wp_on_val.

(**
  By the heap invariant, we can always inspect or modify the heap
  on low values.
*)
Section wp_low_val.
  Context `{heapG Σ}.
  Implicit Types e : expr.
  Implicit Types v : val.

  Lemma wp_low_alloc E e :
    ↑heapN ⊆ E →
    heap_ctx -∗
    WP e @ E ?{{ low }} -∗
    WP Alloc e @ E ?{{ low }}.
  Proof.
    iIntros (?) "Hh He".
    iApply (wp_on_val_alloc with "He [Hh]"). iIntros (v) "Hv".
    iApply (wp_alloc_low with "[$Hh Hv]"); auto.
    iNext. iIntros. by simpl_on_val.
  Qed.

  Lemma wp_low_load E e :
    ↑heapN ⊆ E →
    heap_ctx -∗
    WP e @ E ?{{ low }} -∗
    WP Load e @ E ?{{ low }}.
  Proof.
    iIntros (?) "Hh He".
    iApply (wp_on_val_load with "He [Hh]"). iIntros (l) "Hl".
    by iApply (wp_load_low with "[$Hh Hl]"); auto.
  Qed.

  Lemma wp_low_store E e1 e2:
    ↑heapN ⊆ E →
    heap_ctx -∗
    WP e1 @ E ?{{ low }} -∗
    WP e2 @ E ?{{ low }} -∗
    WP Store e1 e2 @ E ?{{ low }}.
  Proof.
    iIntros (?) "Hh He1 He2".
    iApply (wp_on_val_store with "He1 He2 [Hh]"). iIntros (l1 v2) "Hl1 Hv2".
    iApply (wp_store_low with "[$Hh Hl1 Hv2]"); try auto.
    iNext. iIntros. by simpl_on_val.
  Qed.

  Lemma wp_low_cas E e0 e1 e2 Φ1 :
    ↑heapN ⊆ E →
    heap_ctx -∗
    WP e0 @ E ?{{ low }} -∗
    WP e1 @ E ?{{ Φ1 }} -∗
    WP e2 @ E ?{{ low }} -∗
    WP CAS e0 e1 e2 @ E ?{{ low }}.
  Proof.
    iIntros (?) "Hh He0 He1 He2".
    iApply (wp_on_val_cas with "He0 He1 He2 [Hh]").
    iIntros (l0 v1 v2) "Hl0 Hv2".
    iApply (wp_cas_low with "[$Hh Hl0 Hv2]"); try auto.
    iNext. iIntros. by simpl_on_val.
  Qed.
End wp_low_val.
