From iris.program_logic Require Import hoare.	(* for [on_val_hoare] *)
From iris.heap_lang Require Export lifting.
From iris.heap_lang Require Import proofmode_basics.
Import uPred.

Local Hint Resolve to_of_val.
Local Notation ext R := (pointwise_relation _ R).

(** * Lifting location predicates to value predicates *)
(**
	Given a predicate [Ψ] on locations, the predicate [on_val Ψ]
	on values lifts [Ψ] structurally. If [Ψ] is persistent, so is
	[on_val Ψ].

	[on_val Ψ] can be thought of as a semantic subtype of values
	supporting introduction and elimination rules as follows.

	_Introduction_: Lifted values (i) include all locations
	satisfying [Ψ] and all base values and (ii) are closed under
	function abstraction, pairing, and injections. See
	[on_val_elim], [on_val_rec].

	_Elimination_: Heap resources (q.v.) for lifted locations are
	determined by [Ψ]; otherwise, eliminating a lifted value
	produces a lifted value. See [on_val_app] and friends.
*)
Section definition.
  Context `{irisG heap_lang Σ} (Ψ : loc → iProp Σ).

  (**
    When proving a function [on_val Ψ], one may use any invariant and
    need not make progress.
  *)
  Definition on_val_pre (rec : val -c> iProp Σ) : val -c> iProp Σ := λ v,
    match v with
    | RecV f x e _ => □ ▷ ∀ v, rec v -∗
      WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ rec }}
    | LocV l => Ψ l
    | LitV _ | UnitV => True
    | PairV v1 v2 => ▷(rec v1 ∗ rec v2)
    | InjLV v | InjRV v => ▷(rec v)
    end%I.

  Instance on_val_pre_contractive : Contractive on_val_pre.
  Proof.
    rewrite /on_val_pre=> n rec rec' Hrec ?.
    repeat (f_contractive || f_equiv); apply Hrec.
  Qed.

  Definition on_val_def : val → iProp Σ := fixpoint on_val_pre.
  Definition on_val_aux : { x | x = @on_val_def }. by eexists. Qed.
  Definition on_val := proj1_sig on_val_aux.
  Definition on_val_eq : @on_val = @on_val_def := proj2_sig on_val_aux.

  Lemma on_val_unfold v : on_val_def v ≡ on_val_pre on_val_def v.
  Proof. exact: (fixpoint_unfold on_val_pre). Qed.

  Lemma on_val_elim v :
    on_val v ⊣⊢
    match v with
    | RecV f x e _ => □ ▷ ∀ v, on_val v -∗
      WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ on_val }}
    | LocV l => Ψ l
    | LitV _ | UnitV => True
    | PairV v1 v2 => ▷(on_val v1 ∗ on_val v2)
    | InjLV v | InjRV v => ▷(on_val v)
    end%I.
  Proof. rewrite on_val_eq on_val_unfold. by destruct v. Qed.

  Lemma on_val_rec f x e `{!Closed (f :b: x :b: []) e} :
    on_val (RecV f x e) ⊣⊢
    □ ▷ ∀ v Φ, on_val v -∗ (∀ v', on_val v' -∗ Φ v') -∗
    WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ Φ }}.
  Proof.
    rewrite on_val_elim. iSplit.
    - iIntros "#Hrec !#". iNext. iIntros (v Φ) "Hv". rewrite -wp_wand.
      by iApply ("Hrec" with "Hv").
    - iIntros "#Hrec !#". iNext. iIntros (v) "Hv".
      iApply ("Hrec" with "[$Hv] []"). by iIntros.
  Qed.

  (**
	While we use [on_val_rec] to prove things about lifted
	functions, we characterize them as follows in our paper. (We
	cannot use so-called Texan triples—otherwise favored in our
	Coq development—because they bake in a step of computation.)
  *)
  Lemma on_val_hoare f x e `{!Closed (f :b: x :b: []) e} :
    on_val (RecV f x e) ⊣⊢
    ▷ ∀ v, {{ on_val v }} subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ on_val }}.
  Proof.
    rewrite on_val_elim. iSplit.
    - iIntros "#Hrec". iNext. iIntros (v) "!# Hv". by iApply ("Hrec" with "Hv").
    - iIntros "#Hrec !#". iNext. iIntros (v) "Hv". by iApply ("Hrec" with "Hv").
  Qed.

  Section persistent.
    Context (HΨ : ∀ l, PersistentP (Ψ l)).

    Global Instance on_val_persistent v : PersistentP (on_val v).
    Proof.
      iIntros "Hv". iLöb as "IH" forall (v).
      rewrite on_val_eq on_val_unfold. destruct v;
      try by iDestruct "Hv" as "#Hv".
      - rewrite always_later. iNext. iDestruct "Hv" as "(Hv1&Hv2)".
        iDestruct ("IH" with "* Hv1") as "#Hv1'". iClear "Hv1".
        iDestruct ("IH" with "* Hv2") as "#Hv2'". iClear "Hv2".
        iAlways. by iFrame "#".
      - rewrite always_later. iNext. by iSpecialize ("IH" with "* Hv").
      - rewrite always_later. iNext. by iSpecialize ("IH" with "* Hv").
    Qed.
  End persistent.

  Section timeless.
    Context (HΨ : ∀ l, TimelessP (Ψ l)).

    Global Instance on_val_lit_timeless lit : TimelessP (on_val (LitV lit)).
    Proof.
      by rewrite /TimelessP on_val_eq on_val_unfold pure_timeless.
    Qed.
  End timeless.
End definition.

Section compat.
  Context `{irisG heap_lang Σ}.

  Instance on_val_pre_ne n :
    Proper (ext (dist n) ==> (=) ==> ext (dist n)) on_val_pre.
  Proof. solve_proper. Qed.

  Global Instance on_val_ne n :
    Proper (ext (dist n) ==> (=) ==> dist n) on_val_pre.
  Proof. solve_proper. Qed.

  Global Instance on_val_pre_proper :
    Proper (ext (≡) ==> (=) ==> (≡)) on_val_pre.
  Proof. solve_proper. Qed.
End compat.

(**
	We register no instances that unfold [on_val Ψ] functions.
	Such reasoning is important and should be explicit.
*)

Section proofmode.
  Context `{irisG heap_lang Σ} (Ψ : loc → iProp Σ).

  Global Instance into_and_on_val p v1 v2 :
    IntoAnd p (on_val Ψ (PairV v1 v2)) (▷ on_val Ψ v1) (▷ on_val Ψ v2).
  Proof. apply mk_into_and_sep. by rewrite on_val_elim later_sep. Qed.

  Global Instance from_sep_on_val v1 v2 :
    FromSep (on_val Ψ (PairV v1 v2)) (▷ on_val Ψ v1) (▷ on_val Ψ v2).
  Proof. by rewrite/FromSep (on_val_elim _ (PairV _ _)) later_sep. Qed.

  Global Instance from_assumption_on_val_loc p l Q :
    FromAssumption p (Ψ l) Q → FromAssumption p (on_val Ψ (LocV l)) Q.
  Proof. by rewrite /FromAssumption on_val_elim. Qed.
  Global Instance from_assumption_on_val_inl p v Q :
    FromAssumption p (▷ on_val Ψ v) Q → FromAssumption p (on_val Ψ (InjLV v)) Q.
  Proof. by rewrite /FromAssumption (on_val_elim _ (InjLV _)). Qed.
  Global Instance from_assumption_on_val_inr p v Q :
    FromAssumption p (▷ on_val Ψ v) Q → FromAssumption p (on_val Ψ (InjRV v)) Q.
  Proof. by rewrite /FromAssumption (on_val_elim _ (InjRV _)). Qed.

  Global Instance into_laterN_on_val_pair n v1 v2 Q1 Q2 :
    IntoLaterN n (on_val Ψ v1) Q1 → IntoLaterN n (on_val Ψ v2) Q2 →
    IntoLaterN (S n) (on_val Ψ (PairV v1 v2)) (Q1 ∗ Q2).
  Proof.
    rewrite /IntoLaterN (on_val_elim _ (PairV _ _))=>->->.
    by rewrite -laterN_sep.
  Qed.
  Global Instance into_laterN_on_val_inl n v Q :
    IntoLaterN n (on_val Ψ v) Q → IntoLaterN (S n) (on_val Ψ (InjLV v)) Q.
  Proof. by rewrite /IntoLaterN (on_val_elim _ (InjLV _))=>->. Qed.
  Global Instance into_laterN_on_val_inr n v Q :
    IntoLaterN n (on_val Ψ v) Q → IntoLaterN (S n) (on_val Ψ (InjRV v)) Q.
  Proof. by rewrite /IntoLaterN (on_val_elim _ (InjRV _))=>->. Qed.

  Global Instance from_laterN_on_val_pair v1 v2 :
    FromLaterN 1 (on_val Ψ (PairV v1 v2)) (on_val Ψ v1 ∗ on_val Ψ v2).
  Proof. by rewrite /FromLaterN (on_val_elim _ (PairV _ _)). Qed.
  Global Instance from_laterN_on_val_inl v :
    FromLaterN 1 (on_val Ψ (InjLV v)) (on_val Ψ v).
  Proof. by rewrite /FromLaterN (on_val_elim _ (InjLV _)). Qed.
  Global Instance from_laterN_on_val_inr v :
    FromLaterN 1 (on_val Ψ (InjRV v)) (on_val Ψ v).
  Proof. by rewrite /FromLaterN (on_val_elim _ (InjRV _)). Qed.

  Section loc_except_0.
    Context (HΨ : ∀ l, IsExcept0 (Ψ l)).

    Global Instance on_val_loc_except_0 l : IsExcept0 (on_val Ψ (LocV l)).
    Proof. by rewrite /IsExcept0 on_val_elim is_except_0. Qed.
  End loc_except_0.

  Global Instance on_val_rec_except_0 f x e `{!Closed (f :b: x :b: []) e} :
    IsExcept0 (on_val Ψ (RecV f x e)).
  Proof.
    by rewrite /IsExcept0 on_val_eq on_val_unfold except_0_always
      except_0_later.
  Qed.
  Global Instance on_val_pair_except_0 v1 v2 :
    IsExcept0 (on_val Ψ (PairV v1 v2)).
  Proof. by rewrite /IsExcept0 on_val_eq on_val_unfold except_0_later. Qed.
  Global Instance on_val_inl_except_0 v : IsExcept0 (on_val Ψ (InjLV v)).
  Proof. by rewrite /IsExcept0 on_val_eq on_val_unfold except_0_later. Qed.
  Global Instance on_val_inr_except_0 v : IsExcept0 (on_val Ψ (InjRV v)).
  Proof. by rewrite /IsExcept0 on_val_eq on_val_unfold except_0_later. Qed.
End proofmode.

Typeclasses Opaque on_val.

(** There are no ProofMode classes for "P ≡ True". *)
Ltac simpl_on_val :=
  repeat match goal with
  | |- context [on_val ?Ψ (LocV ?l)] => rewrite (on_val_elim Ψ (LocV l))
  | |- context [on_val ?Ψ (LitV ?lit)] => rewrite (on_val_elim Ψ (LitV lit))
  | |- context [on_val ?Ψ UnitV] => rewrite (on_val_elim Ψ UnitV)
  | |- context [on_val ?Ψ (PairV ?v1 ?v2)] => rewrite (on_val_elim Ψ (PairV v1 v2))
  | |- context [on_val ?Ψ (InjLV ?v)] => rewrite (on_val_elim Ψ (InjLV v))
  | |- context [on_val ?Ψ (InjRV ?v)] => rewrite (on_val_elim Ψ (InjRV v))
  | |- context [(▷ True)%I] => rewrite later_True
  end.
(* Making these pervasive could be a bad idea. *)
Local Hint Extern 5 => simpl_on_val.
Local Hint Extern 1 (uPred_valid True) => unfold uPred_valid.

(** * Eliminating lifted values *)
(**
	These lemmas are useful at the boundary between verified and
	adversarial code.
*)
Section wp_on_val.
  Context `{ownPG heap_lang Σ} (Ψ : loc → iProp Σ).
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Use [wp_stuck_var] for variables. *)

  (** Use [on_val_elim] or [on_val_rec] for functions. *)

  Lemma wp_on_val_app v1 v2 :
    {{{ on_val Ψ v1 ∗ on_val Ψ v2 }}} App (of_val v1) (of_val v2)
    ?{{{ v, RET v; on_val Ψ v }}}.
  Proof.
    iIntros (Φ) "[Hv1 Hv2] HΦ".
    case: (decide (is_rec (of_val v1)))=>Hrec;
      last by iApply wp_stuck_app_nrec.
    destruct (is_rec_val _ Hrec) as (f&x&e&?&->).
    rewrite on_val_rec always_elim.
    wp_apply wp_rec. done. by exists v2. by wp_apply ("Hv1" with "Hv2 HΦ").
  Qed.

  Lemma wp_on_val_app_bind e1 e2 :
    WP e1 ?{{ on_val Ψ }} -∗
    WP e2 ?{{ on_val Ψ }} -∗
    WP App e1 e2 ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_apply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_apply (wp_wand with "He2"). iIntros (v2) "Hv2".
    by wp_apply (wp_on_val_app with "[$Hv1 $Hv2]"); auto.
  Qed.

  Hint Extern 1 (_ -∗ on_val Ψ (LitV ?lit)) =>
    rewrite (on_val_elim Ψ (LitV lit)).
  Hint Extern 1 (_ -∗ on_val Ψ UnitV) =>
    rewrite (on_val_elim Ψ UnitV).
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
    case: op; destruct v1 as [|lit| | | | |];
    repeat (discriminate 1 || injection 1 as <- || destruct lit); auto.
  Qed.

  Lemma wp_on_val_un_op E op v :
    {{{ on_val Ψ v }}} UnOp op (of_val v) @ E ?{{{ v', RET v'; on_val Ψ v' }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    case EV: (un_op_eval op v)=>[v'|]; last by iApply wp_stuck_un_op.
    wp_apply wp_un_op; eauto. iApply "HΦ".
    by iApply (on_val_un_op_eval with "Hv").
  Qed.

  Lemma wp_on_val_un_op_bind E op e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP UnOp op e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_un_op with "Hv"); auto.
  Qed.

  Lemma on_val_bin_op_eval op v1 v2 v3 :
    bin_op_eval op v1 v2 = Some v3 →
    on_val Ψ v1 ∗ on_val Ψ v2 -∗ on_val Ψ v3.
  Proof.
    case: op; destruct v1 as [|lit1| | | | |]; destruct v2 as [|lit2| | | | |];
    repeat (discriminate 1 || injection 1 as <- || destruct lit1
      || destruct lit2); auto.
  Qed.

  Lemma wp_on_val_bin_op E op v1 v2 :
    {{{ on_val Ψ v1 ∗ on_val Ψ v2 }}} BinOp op (of_val v1) (of_val v2) @ E
    ?{{{ v, RET v; on_val Ψ v }}}.
  Proof.
    iIntros (Φ) "[Hv1 Hv2] HΦ".
    case EV: (bin_op_eval op v1 v2)=>[v'|]; last by iApply wp_stuck_bin_op.
    wp_apply wp_bin_op; eauto. iApply "HΦ".
    by iApply (on_val_bin_op_eval with "[$Hv1 $Hv2]").
  Qed.

  Lemma wp_on_val_bin_op_bind E op e1 e2 :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    WP BinOp op e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_apply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_apply (wp_wand with "He2"). iIntros (v2) "Hv2".
    by iApply (wp_on_val_bin_op with "[$Hv1 $Hv2]"); auto.
  Qed.

  Lemma wp_any_if E v e1 e2 Φ :
    ▷ (WP e1 @ E ?{{ Φ }} ∧ WP e2 @ E ?{{ Φ }}) -∗
    WP If (of_val v) e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "Hei".
    case: (decide (is_bool (of_val v)))=>Hbool; last by iApply wp_stuck_if.
    case: Hbool=>-[]->.
    - iApply wp_if_true. iNext. by iDestruct "Hei" as "[? _]".
    - iApply wp_if_false. iNext. by iDestruct "Hei" as "[_ ?]".
  Qed.

  Lemma wp_any_if_bind E e0 e1 e2 Φ0 Φ :
    WP e0 @ E ?{{ Φ0 }} -∗
    ▷ (WP e1 @ E ?{{ Φ }} ∧ WP e2 @ E ?{{ Φ }}) -∗
    WP If e0 e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He0 Hei".
    wp_apply (wp_wand with "He0"). iIntros (v) "_".
    by iApply (wp_any_if with "Hei").
  Qed.

  Lemma wp_on_val_pair E v1 v2 :
    on_val Ψ v1 -∗ on_val Ψ v2 -∗
    WP Pair (of_val v1) (of_val v2) @ E ?{{ on_val Ψ }}.
  Proof. iIntros "Hv1 Hv2". wp_value. simpl_on_val. by iFrame. Qed.

  Lemma wp_on_val_pair_bind E e1 e2 :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ on_val Ψ }} -∗
    WP Pair e1 e2 @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He1 He2".
    wp_apply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_apply (wp_wand with "He2"). iIntros (v2) "Hv2".
    by iApply (wp_on_val_pair with "Hv1 Hv2").
  Qed.

  Lemma wp_on_val_fst E v :
    {{{ on_val Ψ v }}} Fst (of_val v) @ E ?{{{ v', RET v'; on_val Ψ v' }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    case: (decide (is_pair (of_val v)))=>Hp; last by iApply wp_stuck_fst.
    destruct (is_pair_val _ Hp) as (v1&v2&->).
    wp_apply wp_fst; [done|by exists v2|]. iApply "HΦ".
    by iDestruct "Hv" as "(?&_)".
  Qed.

  Lemma wp_on_val_fst_bind E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP Fst e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He".
    wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_fst with "Hv"); auto.
  Qed.

  Lemma wp_on_val_snd E v :
    {{{ on_val Ψ v }}} Snd (of_val v) @ E ?{{{ v', RET v'; on_val Ψ v' }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    case: (decide (is_pair (of_val v)))=>Hp; last by iApply wp_stuck_snd.
    destruct (is_pair_val _ Hp) as (v1&v2&->).
    wp_apply wp_snd; [by exists v1|done|]. iApply "HΦ".
    by iDestruct "Hv" as "(_&?)".
  Qed.

  Lemma wp_on_val_snd_bind E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP Snd e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_snd with "Hv"); auto.
  Qed.

  Lemma wp_on_val_inl E v :
    on_val Ψ v -∗
    WP InjL (of_val v) @ E ?{{ on_val Ψ }}.
  Proof. iIntros "Hv". wp_value. simpl_on_val. by iNext. Qed.

  Lemma wp_on_val_inl_bind E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP InjL e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_inl with "Hv").
  Qed.

  Lemma wp_on_val_inr E v :
    on_val Ψ v -∗
    WP InjR (of_val v) @ E ?{{ on_val Ψ }}.
  Proof. iIntros "Hv". wp_value. simpl_on_val. by iNext. Qed.

  Lemma wp_on_val_inr_bind E e :
    WP e @ E ?{{ on_val Ψ }} -∗
    WP InjR e @ E ?{{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_inr with "Hv").
  Qed.

  Lemma wp_on_val_case E v e1 e2 Φ :
    on_val Ψ v -∗
    ▷ (∀ v0, on_val Ψ v0 -∗
      WP App e1 (of_val v0) @ E ?{{ Φ }} ∧
      WP App e2 (of_val v0) @ E ?{{ Φ }}) -∗
    WP Case (of_val v) e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "Hv Hk".
    case: (decide (is_inl (of_val v) ∨ is_inr (of_val v)))=>Hc;
      last by iApply wp_stuck_case.
    case: Hc=>[Hinl | Hinr].
    - destruct (is_inl_val _ Hinl) as (v0&->). simpl.
      iApply wp_case_inl; first by exists v0. iNext.
      setoid_rewrite and_elim_l. by iApply ("Hk" with "Hv").
    - destruct (is_inr_val _ Hinr) as (v0&->). simpl.
      iApply wp_case_inr; first by exists v0. iNext.
      setoid_rewrite and_elim_r. by iApply ("Hk" with "Hv").
  Qed.

  Lemma wp_on_val_case_bind E e0 e1 e2 Φ :
    WP e0 @ E ?{{ on_val Ψ }} -∗
    ▷ (∀ v0, on_val Ψ v0 -∗
      WP App e1 (of_val v0) @ E ?{{ Φ }} ∧
      WP App e2 (of_val v0) @ E ?{{ Φ }}) -∗
    WP Case e0 e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He0 Hk". wp_apply (wp_wand with "He0"). iIntros (v) "Hv".
    by iApply (wp_on_val_case with "Hv").
  Qed.

  (** We don't need compatibility for [Assert e]. *)

  Lemma wp_on_val_fork p E e Φ :
    ▷ WP e @ p; ⊤ {{ Φ }} -∗
    WP Fork e @ p; E {{ on_val Ψ }}.
  Proof.
    iIntros "He". wp_apply wp_fork. iSplitR. by simpl_on_val.
    by iApply (wp_wand with "He"); auto.
  Qed.

  (** The heap may be inspected or modified according to [Ψ]. *)

  Lemma wp_on_val_alloc_bind p E e Φ :
    WP e @ p; E {{ Φ }} -∗
    (∀ v, Φ v -∗ WP Alloc (of_val v) @ p; E {{ on_val Ψ }}) -∗
    WP Alloc e @ p; E {{ on_val Ψ }}.
  Proof.
    iIntros "He Halloc".
    wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply ("Halloc" with "Hv").
  Qed.

  Lemma wp_on_val_load E v Φ :
    on_val Ψ v -∗
    (∀ l, Ψ l -∗ WP Load (Loc l) @ E ?{{ Φ }}) -∗
    WP Load (of_val v) @ E ?{{ Φ }}.
  Proof.
    iIntros "Hv Hload".
    case: (decide (is_loc (of_val v)))=>Hl; last by iApply wp_stuck_load.
    destruct (is_loc_val _ Hl) as (l&->). rewrite on_val_elim.
    by iApply ("Hload" with "Hv").
  Qed.

  Lemma wp_on_val_load_bind E e Φ :
    WP e @ E ?{{ on_val Ψ }} -∗
    (∀ l, Ψ l -∗ WP Load (Loc l) @ E ?{{ Φ }}) -∗
    WP Load e @ E ?{{ Φ }}.
  Proof.
    iIntros "He Hload".
    wp_apply (wp_wand with "He"). iIntros (v) "Hv".
    by iApply (wp_on_val_load with "Hv Hload").
  Qed.

  Lemma wp_on_val_store E v1 v2 Φ :
    on_val Ψ v1 -∗
    (∀ l1, Ψ l1 -∗ WP Store (Loc l1) (of_val v2) @ E ?{{ Φ }}) -∗
    WP Store (of_val v1) (of_val v2) @ E ?{{ Φ }}.
  Proof.
    iIntros "Hv1 Hstore".
    case: (decide (is_loc (of_val v1)))=>Hl; last by iApply wp_stuck_store.
    destruct (is_loc_val _ Hl) as (l1&->). rewrite on_val_elim.
    by iApply ("Hstore" with "Hv1").
  Qed.

  Lemma wp_on_val_store_bind E e1 e2 Φ2 Φ :
    WP e1 @ E ?{{ on_val Ψ }} -∗
    WP e2 @ E ?{{ Φ2 }} -∗
    (∀ l1 v2, Ψ l1 -∗ Φ2 v2 -∗
     WP Store (Loc l1) (of_val v2) @ E ?{{ Φ }}) -∗
    WP Store e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He1 He2 Hstore".
    wp_apply (wp_wand with "He1"). iIntros (v1) "Hv1".
    wp_apply (wp_wand with "He2"). iIntros (v2) "Hv2".
    iApply (wp_on_val_store with "Hv1"). iIntros (l) "Hl".
    by iApply ("Hstore" with "Hl Hv2").
  Qed.

  Lemma wp_on_val_cas E v0 v1 v2 Φ :
    on_val Ψ v0 -∗
    (∀ l0, Ψ l0 -∗
     WP CAS (Loc l0) (of_val v1) (of_val v2) @ E ?{{ Φ }}) -∗
    WP CAS (of_val v0) (of_val v1) (of_val v2) @ E ?{{ Φ }}.
  Proof.
    iIntros "Hv0 Hcas".
    case: (decide (is_loc (of_val v0)))=>Hl; last by iApply wp_stuck_cas.
    destruct (is_loc_val _ Hl) as (l0&->). rewrite on_val_elim.
    iApply ("Hcas" with "Hv0").
  Qed.

  Lemma wp_on_val_cas_bind E e0 e1 e2 Φ1 Φ2 Φ :
    WP e0 @ E ?{{ on_val Ψ }} -∗
    WP e1 @ E ?{{ Φ1 }} -∗
    WP e2 @ E ?{{ Φ2 }} -∗
    (∀ l0 v1 v2, Ψ l0 -∗ Φ2 v2 -∗
     WP CAS (Loc l0) (of_val v1) (of_val v2) @ E ?{{ Φ }}) -∗
    WP CAS e0 e1 e2 @ E ?{{ Φ }}.
  Proof.
    iIntros "He0 He1 He2 Hcas".
    wp_apply (wp_wand with "He0"). iIntros (v0) "Hv0".
    wp_apply (wp_wand with "He1"). iIntros (v1) "_".
    wp_apply (wp_wand with "He2"). iIntros (v2) "Hv2".
    iApply (wp_on_val_cas with "Hv0"). iIntros (l) "Hl".
    by iApply ("Hcas" with "Hl Hv2").
  Qed.
End wp_on_val.
