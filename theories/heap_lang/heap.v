From iris.prelude Require Import gmultiset.
From iris.algebra Require Import auth gmap csum agree.
From iris.algebra Require Export gset frac.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import own auth fractional.
From iris.base_logic Require Import big_op.
From iris.heap_lang Require Export lifting.
From iris.heap_lang Require addenda.
From iris.proofmode Require Import tactics.
Import uPred.
Import addenda.fin_maps.
Import addenda.option addenda.gmap addenda.csum.
Import addenda.auth.

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
Section on_val.
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
    - iIntros "#Hv !#". iNext. iIntros (v2 Φ) "Hv2". rewrite -wp_wand.
      by iApply ("Hv" with "[$Hv2]").
    - iIntros "#Hv !#". iNext. iIntros (v2) "Hv2".
      iApply ("Hv" with "[$Hv2] []"). by iIntros.
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
End on_val.

Section on_val_ne.
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
End on_val_ne.

(**
	We register no instances that unfold [on_val Ψ] functions.
	Such reasoning is important and should be explicit.
*)

Section on_val_proofmode_classes.
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
End on_val_proofmode_classes.

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

(** The CMRA we need. *)
Local Notation heap := (gmap loc val).
Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT :=
  gmapUR loc (csumR (prodR fracR (agreeR valC)) unitR).
Local Notation Hval q v := (Cinl (q%Qp, to_agree v)).
Local Notation Lval := (Cinr ()).

Class heapG Σ := HeapG {
  heap_ownP_inG :> ownPG heap_lang Σ;
  heap_inG :> authG Σ heapUR;
  heap_name : gname
}.

Class heapPreG Σ := HeapPreG {
  heap_preG_ownP_inG : ownPPreG heap_lang Σ;
  heap_preG_inG : authG Σ heapUR
}.
(*
 * Lower priority than heapG's instances so the occurrence of
 * [heap_ctx] in the statement of [heap_adequacy] refers to the
 * "inner" [heapG] rather than the "outer" [heapPreG].
 *)
Existing Instance heap_preG_ownP_inG | 30.
Existing Instance heap_preG_inG | 30.

Definition heapΣ : gFunctors := #[ownPΣ state; authΣ heapUR].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [??]%subG_inv; constructor; apply _. Qed.

(** * Heap resources and invariant *)
Section definitions.
  Context `{ownPG heap_lang Σ, authG Σ heapUR} (γ : gname).
  Implicit Types l : loc.
  Implicit Types q : Qp.
  Implicit Types v : val.
  Implicit Types h : heap.

  (** High locations. *)
  Definition mapsto_def l q v : iProp Σ := auth_own γ {[l := Hval q v]}.
  Definition mapsto_aux : { x | x = @mapsto_def }. by eexists. Qed.
  Definition mapsto := proj1_sig mapsto_aux.
  Definition mapsto_eq : @mapsto = @mapsto_def := proj2_sig mapsto_aux.

  (** Low locations. *)
  Definition lowloc'_def l : iProp Σ := auth_own γ {[l := Lval]}.
  Definition lowloc'_aux : { x | x = @lowloc'_def }. by eexists. Qed.
  Definition lowloc' := proj1_sig lowloc'_aux.
  Definition lowloc'_eq : @lowloc' = @lowloc'_def := proj2_sig lowloc'_aux.

  (** Low values. *)
  Notation lowval := (on_val lowloc').

  (**
    Invariant: The state is good and maps every high location to its
    value and every low location to a low value.
  *)
  Definition to_high : heap → heapUR := fmap (λ v, Hval 1 v).
  Definition to_low : heap → heapUR  := fmap (λ _, Lval).
  Definition to_heap (a : heap * heap) : heapUR :=
    let: (h, h') := a in to_high h ⋅ to_low h'.
  Definition hinv' (a : heap * heap) : iProp Σ :=
    let: (h, h') := a in
    (ownP (good_state (h ∪ h')) ∗ [∗ map] v ∈ h', lowval v)%I.

  Lemma hinv_alloc h : ownP (good_state h) -∗ ▷ hinv' (h, ∅).
  Proof.
    rewrite /hinv' right_id big_sepM_empty right_id. exact: later_intro.
  Qed.

  Lemma to_heap_valid h : ✓ to_heap (h, ∅).
  Proof. move=>l. rewrite lookup_op !lookup_fmap. by case (h !! l). Qed.

  Definition heap_ctx' : iProp Σ := auth_ctx γ heapN to_heap hinv'.
  Global Instance heap_ctx_persistent : PersistentP heap_ctx'.
  Proof. apply _. Qed.
End definitions.
Typeclasses Opaque mapsto lowloc'.
(* PDS: heap_ctx' not opaque because we lack some instances. *)
Instance: Params (@mapsto) 2.
Instance: Params (@lowloc') 2.
Instance: Params (@heap_ctx') 3.

Notation "l ↦{ q } v" := (mapsto heap_name l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (mapsto heap_name l 1 v) (at level 20) : uPred_scope.

Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Notation lowloc := (lowloc' heap_name).
Notation heap_ctx := (heap_ctx' heap_name).
Local Notation hinv := (hinv' heap_name).

(** Allocating the invariant. *)
(** We cannot use [auth_alloc] as [hinv] depends on the ghost name. *)
Lemma heap_ctx_alloc `{ownPG heap_lang Σ, authG Σ heapUR} E h :
  ownP (good_state h) ={E}=∗ ∃ γ, heap_ctx' γ.
Proof.
  iIntros "Hσ". set h' := to_heap (h, ∅).
  iMod (own_alloc (Auth (Excl' h') h')) as (γ) "Ha".
  { split. done. exact: to_heap_valid. }
  set hinv_γ := @hinv' _ _ _ γ.
  iRevert "Ha"; rewrite auth_both_op; iIntros "[Ha _]".
  iDestruct (@hinv_alloc _ _ _ γ with "Hσ") as "Hσ".
  iMod (inv_alloc heapN _ (auth_inv γ to_heap hinv_γ) with "[Ha Hσ]") as "#?".
  { iNext. rewrite/auth_inv. iExists (h, ∅). by iFrame. }
  iModIntro. iExists γ. by rewrite/heap_ctx'/auth_ctx.
Qed.

(** Observing good states. *)
Lemma heap_ctx_is_good `{heapG Σ} E :
 ↑heapN ⊆ E → heap_ctx ={E,∅}=∗ ∃ σ, ownP σ ∧ ⌜is_good σ⌝.
Proof.
  iIntros (?) "Hinv". iMod (fupd_intro_mask' _ (↑heapN)) as "_"; first done.
  iMod (auth_empty heap_name) as "Ha".
  iMod (auth_open with "[$Hinv $Ha]") as ([h h']) "(_&[>Hh _]&_)";
    first done.
  iExists _; iFrame. by rewrite subseteq_empty_difference_L.
Qed.

(** * Low integrity predicates *)
Class LowIntegrity Σ (A : Type) := Low {
  low : A → iProp Σ;
  low_persistent a :> PersistentP (low a);
  low_ne n :> Proper ((=) ==> dist n) low
}.
Arguments Low {_ _} _ _ _.
Arguments low {_ _ _} _ : simpl never.
Instance: Params (@low) 3.

Instance low_proper `{LowIntegrity Σ A} : Proper ((=) ==> (≡)) low.
Proof. solve_proper. Qed.

(*
Class SyntacticallyLow Σ (A : Type) := SynLow {
  synlow : A → iProp Σ;
  synlow_timeless a :> TimelessP (synlow a);
  synlow_persistent a :> PersistentP (synlow a);
  synlow_ne n :> Proper ((=) ==> dist n) synlow
}.
Arguments SynLow {_ _} _ _ _ _.
Arguments synlow {_ _ _} _ : simpl never.
Instance: Params (@synlow) 3.

Instance synlow_proper `{SyntacticallyLow Σ A} :
  Proper ((=) ==> (≡)) synlow.
Proof. solve_proper. Qed.
*)

Section low.
  Context `{heapG Σ}.

  (**
    Locations start off high and may be marked low by the
    (irreversible) ghost move [heap_mark_low].
  *)
  Global Instance lowloc_persistent l : PersistentP (lowloc l).
  Proof. rewrite lowloc'_eq /lowloc'_def. apply _. Qed.
  Global Instance loc_low : LowIntegrity Σ loc := Low lowloc _ _.
  Global Instance loc_low_timeless (l : loc) : TimelessP (low l).
  Proof. rewrite /low/= lowloc'_eq /lowloc'_def. apply _. Qed.

  Lemma low_loc l : low l ⊣⊢ lowloc l. Proof. by []. Qed.

  (**
    A (syntactically) low expression contains neither assertions nor
    high locations. We reserve assertions for verified code.
  *)
  Definition lowexpr : expr → iProp Σ :=
    fix rec e := match e with
    | Var _ | Lit _ | Unit => True
    | Assert _ => False
    | Loc l => low l
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e | InjR e
    | Fork e | Alloc e | Load e
      => rec e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 => rec e1 ∗ rec e2
    | If e1 e2 e3 | Case e1 e2 e3 | CAS e1 e2 e3
      => rec e1 ∗ rec e2 ∗ rec e3
    end%I.
  Global Instance lowexpr_persistent e : PersistentP (lowexpr e).
  Proof.
    rewrite/lowexpr; elim: e=>//; rewrite-/lowexpr; by apply _.
  Qed.
  Global Instance lowexpr_low : LowIntegrity Σ expr := Low lowexpr _ _.
  Global Instance lowexpr_low_timeless (e : expr) : TimelessP (low e).
  Proof.
    rewrite/lowexpr; elim: e=>//; rewrite-/lowexpr; by apply _.
  Qed.

  Lemma low_expr e :
    low e ⊣⊢
    match e with
    | Var _ | Lit _ | Unit => True
    | Assert _ => False
    | Loc l => low l
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e | InjR e
    | Fork e | Alloc e | Load e
      => low e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 => low e1 ∗ low e2
    | If e1 e2 e3 | Case e1 e2 e3 | CAS e1 e2 e3
      => low e1 ∗ low e2 ∗ low e3
    end.
  Proof. by case: e. Qed.

  (** Low values lift low locations to values. *)
  Global Instance val_low : LowIntegrity Σ val := Low (on_val lowloc) _ _.

  Lemma low_val_eq v : low v ⊣⊢ on_val lowloc v. Proof. by []. Qed.

  Lemma low_val v :
    low v ⊣⊢
    match v with
    | RecV f x e _ => □ ▷ ∀ v, low v -∗
      WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ low }}
    | LocV l => low l
    | LitV _ | UnitV => True
    | PairV v1 v2 => ▷ (low v1 ∗ low v2)
    | InjLV v | InjRV v => ▷ low v
    end.
  Proof. by rewrite low_val_eq on_val_elim. Qed.

  Lemma low_rec f x e `{!Closed (f :b: x :b: []) e} :
    low (RecV f x e) ⊣⊢
    □ ▷ ∀ v Φ, low v -∗ (∀ v', low v' -∗ Φ v') -∗
    WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ Φ }}.
  Proof. by rewrite low_val_eq on_val_rec. Qed.

  Global Instance low_val_loc_timeless l : TimelessP (low (LocV l)).
  Proof. by rewrite /TimelessP low_val timelessP. Qed.
  Global Instance low_val_rec_except_0 f x e `{!Closed (f :b: x :b: []) e} :
    IsExcept0 (low (RecV f x e)).
  Proof. apply _. Qed.
  Global Instance low_val_pair_except_0 v1 v2 : IsExcept0 (low (PairV v1 v2)).
  Proof. apply _. Qed.
  Global Instance low_val_inl_except_0 v : IsExcept0 (low (InjLV v)).
  Proof. apply _. Qed.
  Global Instance low_val_inr_except_0 v : IsExcept0 (low (InjRV v)).
  Proof. apply _. Qed.
End low.

Ltac simpl_low :=
  repeat match goal with
  | |- context [low (LocV ?l)] => rewrite (low_val (LocV l))
  | |- context [low (LitV ?lit)] => rewrite (low_val (LitV lit))
  | |- context [low UnitV] => rewrite (low_val UnitV)
  | |- context [low (PairV ?v1 ?v2)] => rewrite (low_val (PairV v1 v2))
  | |- context [low (InjLV ?v)] => rewrite (low_val (InjLV v))
  | |- context [low (InjRV ?v)] => rewrite (low_val (InjRV v))
  | |- context [(▷ True)%I] => rewrite later_True
  end.
Local Hint Extern 5 => simpl_low.

(** * Bookkeeping lemmas *)
Section bookkeeping.
  Context `{heapG Σ}.
  Implicit Types l : loc.
  Implicit Types q : Qp.
  Implicit Types v : val.
  Implicit Types h : heap.

  Remark to_heap_disjoint h h' : ✓ to_heap (h, h') → h ⊥ₘ h'.
  Proof.
    move=>Hv. rewrite map_disjoint_spec=>l ? ? EQ EQ'; move/(_ l): Hv.
    by rewrite /to_heap lookup_op /to_high /to_low 2!lookup_fmap EQ EQ'.
  Qed.

  Lemma lookup_to_high_None h l : h !! l = None → to_high h !! l = None.
  Proof. by rewrite /to_high lookup_fmap=> ->. Qed.
  Lemma lookup_to_low_None h l : h !! l = None → to_low h !! l = None.
  Proof. by rewrite /to_low lookup_fmap=> ->. Qed.
  Lemma lookup_to_heap_None h h' l :
    (h ∪ h') !! l = None → to_heap (h, h') !! l = None.
  Proof.
    move=> /lookup_union_None [??].
    by rewrite lookup_op lookup_to_high_None ?lookup_to_low_None.
  Qed.

  Lemma lookup_to_high_Some h l v :
    h !! l = Some v → to_high h !! l = Some(Hval 1 v).
  Proof. by rewrite /to_high lookup_fmap=>->. Qed.
  Lemma lookup_to_low_Some h l v : h !! l = Some v → to_low h !! l = Some Lval.
  Proof. by rewrite /to_low lookup_fmap=>->. Qed.
  Lemma lookup_to_heap_Some h h' l v :
    h !! l = Some v → h' !! l = None → to_heap (h, h') !! l = Some (Hval 1 v).
  Proof.
    rewrite /to_heap lookup_op.
    by move=>/lookup_to_high_Some->/lookup_to_low_None->.
  Qed.

  Lemma to_heap_high_included h h' l q v :
    ✓ to_heap (h, h') → {[l := Hval q v]} ≼ to_heap (h, h') →
    h !! l = Some v ∧ h' !! l = None.
  Proof.
    rewrite singleton_included => /(_ l) Hv [] u []; move: Hv.
    rewrite !lookup_op /to_high /to_low !lookup_fmap.
    case EQ: (h !! l)=>[vh|]; case EQ': (h' !! l)=>[vl|] /=.
    - by rewrite -Some_op Some_valid.
    - rewrite right_id.
      intros Hv (?&Heq&Heq')%(equiv_Some_inv_r _ _ u) Hinc; last done.
      apply (inj Some) in Heq. move: Heq Heq' Hinc => <- => Heq.
      case/Some_included.
      + by move: Heq=><- /csum_equivE [] _ /= /to_agree_inj
          /leibniz_equiv_iff ->.
      + move=> Hinc; move: Hinc Heq.
        case/csum_included; first by move=>->/csum_equivE.
        case; last by move=> [?] [?] [].
        move=> [[qa ua]] [[qb ub]] [] [<-<-] [] ->.
        move=> /prod_included/= [] _ Hinc.
        move=>/csum_equivE/= [] /= _ => Heq.
        rewrite <- Heq in Hinc.
        by move: Hinc => /to_agree_included /leibniz_equiv_iff ->.
    - rewrite left_id => _ Heq. apply (inj Some) in Heq. rewrite <- Heq.
      case/Some_included; first by move=>/csum_equivE.
      case/csum_included; first done.
      case. by move=> [?] [?] [] _ []. by move=> [?] [?] [].
    - rewrite right_id. by move=> _ /option_equivE.
  Qed.

  Lemma to_heap_low_included h h' l :
    ✓ to_heap (h, h') → {[l := Lval]} ≼ to_heap (h, h') →
    h !! l = None ∧ is_Some(h' !! l).
  Proof.
    rewrite singleton_included => /(_ l) Hv [] u []; move: Hv.
    rewrite !lookup_op /to_high /to_low !lookup_fmap.
    case EQ: (h !! l)=>[vh|]; case EQ': (h' !! l)=>[vl|] /=.
    - by rewrite -Some_op Some_valid.
    - rewrite right_id => _ Heq Hinc. apply Some_equiv_inj in Heq.
      case/Some_included: Hinc Heq; first by move=><- /csum_equivE.
      case/csum_included; first by move=>-> /csum_equivE.
      case; first by move=> [?] [?] [].
      by move=> [?] [?] [] _ [] -> _ /csum_equivE.
    - move=>_ _ _. split. done. by exists vl.
    - rewrite right_id. by move=> _ /option_equivE.
  Qed.

  Lemma to_heap_high_insert h h' l v :
    h' !! l = None →
    to_heap (<[l:=v]> h, h') = <[l:=Hval 1 v]>(to_heap (h, h')).
  Proof.
    move=>?. rewrite /to_heap /to_high fmap_insert. apply/map_eq => l'.
    case: (decide (l = l'))=> [<-|?].
    - rewrite insert_op_l //. by rewrite lookup_to_low_None.
    - by rewrite lookup_op lookup_insert_ne // lookup_insert_ne // -lookup_op.
  Qed.

  Lemma to_heap_low_insert h h' l v :
    h !! l = None → to_heap (h, <[l:=v]> h') = <[l:=Lval]>(to_heap (h, h')).
  Proof.
    move=>?. rewrite /to_heap /to_low fmap_insert. apply/map_eq=> l'.
    case: (decide (l = l'))=> [<-|?].
    - rewrite insert_op_r //. by rewrite lookup_to_high_None.
    - by rewrite lookup_op lookup_insert_ne // lookup_insert_ne // -lookup_op.
  Qed.

  Lemma to_heap_low_insert_override h h' l v1 v2 :
    h' !! l = Some v1 → to_heap (h, h') = to_heap (h, <[l:=v2]> h').
  Proof.
    move=>Hlow. apply/map_eq=> l'. rewrite 2!lookup_op. f_equiv.
    rewrite /to_low 2!lookup_fmap. case: (decide (l = l')) =>[<-|?].
    - by rewrite Hlow lookup_insert.
    - by rewrite lookup_insert_ne.
  Qed.

  Lemma to_heap_delete h h' l :
    h' !! l = None →
    delete l (to_heap (h, h')) = to_heap (delete l h, h').
  Proof.
    move=>Hdom. rewrite /to_heap /to_high fmap_delete.
    apply/map_eq=> l'. rewrite lookup_op. case: (decide (l = l'))=> [<-|?].
    - by rewrite !lookup_delete lookup_to_low_None.
    - by rewrite lookup_delete_ne // lookup_delete_ne // -lookup_op.
  Qed.

  Lemma to_heap_mark_low h h' l v :
    ✓ to_heap (h, h') → {[l := Hval 1 v]} ≼ to_heap (h, h') →
    (to_heap (h, h'), {[l := Hval 1 v]}) ~l~>
    (to_heap (delete l h, <[l:=v]> h'), {[l := Lval]}).
  Proof.
    move=>Hv /to_heap_high_included -/(_ Hv)[_ ?].
    etransitivity; first by apply delete_singleton_local_update, _.
    rewrite to_heap_delete // to_heap_low_insert; last by rewrite lookup_delete.
    apply alloc_singleton_local_update; last done.
    apply lookup_to_heap_None, lookup_union_None. by rewrite lookup_delete.
  Qed.

  Lemma to_heap_alloc_high h h' l v :
    (h ∪ h') !! l = None →
    (to_heap (h, h'), ∅) ~l~> (to_heap (<[l:=v]> h, h'), {[l := Hval 1 v]}).
  Proof.
    move=>Hdom.
    rewrite to_heap_high_insert; last by move: Hdom=>/lookup_union_None[].
    apply alloc_singleton_local_update; last done.
    by apply lookup_to_heap_None.
  Qed.

  Lemma to_heap_store_high h h' l v1 v2 :
    ✓ to_heap (h, h') → h !! l = Some v1 → h' !! l = None →
    (to_heap (h, h'), {[l := Hval 1 v1]}) ~l~>
    (to_heap (<[l:=v2]> h, h'), {[l := Hval 1 v2]}).
  Proof.
    move=>???. rewrite to_heap_high_insert //.
    eapply singleton_local_update; first exact: lookup_to_heap_Some.
    exact: exclusive_local_update.
  Qed.

  Lemma hinv_intro h h' :
    ownP (good_state (h ∪ h')) -∗ ([∗ map] v ∈ h', low v) -∗ hinv (h, h').
  Proof. rewrite/hinv. by iIntros; iFrame. Qed.

  Lemma hinv_high h h' l v :
    ownP (good_state (<[l:=v]> (h ∪ h'))) -∗ ([∗ map] v ∈ h', low v) -∗
    hinv (<[l:=v]> h, h').
  Proof. rewrite/hinv insert_union_l. by iIntros; iFrame. Qed.

  Lemma hinv_mark_low h h' l v :
    ✓ to_heap (h, h') → {[l := Hval 1 v]} ≼ to_heap (h, h') →
    ▷ ownP (good_state (h ∪ h')) -∗
    ▷ low v -∗ ▷ ([∗ map] v' ∈ h', low v') -∗ ▷ hinv (delete l h, <[l:=v]>h').
  Proof.
    move=>Hv /to_heap_high_included -/(_ Hv)[??]. rewrite/hinv.
    iIntros "Hh Hv Hlow". rewrite -delete_insert_union //.
    iFrame. rewrite 2!big_sepM_later big_sepM_insert //. by iFrame.
  Qed.

  Lemma hinv_store_low h h' l v1 v2 :
    h !! l = None → h' !! l = Some v1 →
    ownP (good_state (<[l:=v2]> (h ∪ h'))) -∗
    ([∗ map] v ∈ h', low v) -∗ low v2 -∗ hinv (h, <[l:=v2]> h').
  Proof.
    move=>??.
    rewrite /hinv insert_union_r // big_sepM_insert_override_2 //.
    iIntros "? Hlow ?". iFrame. iApply "Hlow". eauto.
  Qed.
End bookkeeping.

(** * Heap interface *)
Section heap.
  Context `{heapG Σ}.
  Implicit Types l : loc.
  Implicit Types q : Qp.
  Implicit Types v : val.
  Implicit Types h : heap.

  (** High and low locations are disjoint. *)
  Lemma high_not_low l q v : l ↦{q} v ∗ low l ⊢ False.
  Proof.
    by rewrite mapsto_eq low_loc lowloc'_eq
      -auth_own_op auth_own_valid discrete_valid
      op_singleton singleton_valid.
  Qed.

  (** High locations enjoy their usual properties. *)
  Global Instance mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite mapsto_eq. apply _. Qed.
  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q. by rewrite mapsto_eq -auth_own_op
      op_singleton Cinl_op pair_op agree_idemp.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite mapsto_eq -auth_own_op auth_own_valid discrete_valid
      op_singleton singleton_valid Cinl_op pair_op.
    by f_equiv=> -[] _ /agree_op_inv/to_agree_inj/leibniz_equiv_iff.
  Qed.

  Global Instance heap_ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (mapsto_agree with "[$H1 $H2]") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance heap_ex_mapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_valid l q v : l ↦{q} v ⊢ ✓ q.
  Proof.
    rewrite mapsto_eq /mapsto_def auth_own_valid !discrete_valid
      singleton_valid.
    by apply pure_mono=> -[].
  Qed.
  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "[H1 H2]". iDestruct (mapsto_agree with "[$H1 $H2]") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.

  (** High locations containing low values may be marked low. *)
  Lemma heap_mark_low E l v :
    ↑heapN ⊆ E →
    heap_ctx -∗ ▷ l ↦ v -∗ ▷ low v ={E}=∗ low l.
  Proof.
    iIntros (?) "#Hinv >Hl Hv". rewrite /heap_ctx mapsto_eq /mapsto_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    iDestruct (hinv_mark_low with "Hh Hv Hlow") as "Hh"; [done|done|].
    iMod ("Hcl" with "* [Hh]") as "Ha".
    - iFrame. iPureIntro. exact: to_heap_mark_low.
    - by rewrite low_loc lowloc'_eq /lowloc'_def.
  Qed.

  (** Heap rules for high and low locations. *)
  Lemma wp_alloc p E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx }}} Alloc e @ p; E {{{ l, RET LocV l; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "#Hinv HΦ". rewrite /heap_ctx.
    iMod (auth_empty heap_name) as "Ha".
    iMod (auth_open with "[$Hinv $Ha]") as ([h h']) "(%&[Hh Hlow]&Hcl)";
      first done.
    iApply (wp_alloc_pst with "Hh"); first done. iNext. iIntros (l) "[% Hh]".
    iDestruct (hinv_high with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha".
    - iFrame. iPureIntro. exact: to_heap_alloc_high.
    - iApply "HΦ". by rewrite mapsto_eq /mapsto_def.
  Qed.

  Lemma wp_alloc_low p E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low v }}} Alloc e @ p; E
    {{{ l, RET LocV l; low l }}}.
  Proof.
    iIntros (?? Φ) "[#Hinv Hv] HΦ". rewrite -wp_fupd.
    iApply (wp_alloc with "Hinv"); eauto.
    iNext. iIntros (l) "Hl". rewrite [(l ↦ v)%I]later_intro [low _]later_intro.
    iDestruct (heap_mark_low with "Hinv Hl Hv") as "Hl"; first done.
    by iApply ("HΦ" with "Hl").
  Qed.

  Lemma wp_load p E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Load (Loc l) @ p; E
    {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx mapsto_eq /mapsto_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_high_included h h' l q v) => // ??.
    iApply (wp_load_pst with "Hh"); [done|exact: lookup_union_Some_l|].
    iNext; iIntros "Hh". iDestruct (hinv_intro with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha"; first by eauto. by iApply "HΦ".
  Qed.

  Lemma wp_load_low p E l :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low l }}} Load (Loc l) @ p; E
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx low_loc lowloc'_eq /lowloc'_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v ?].
    iApply (wp_load_pst with "Hh"); [done|exact: lookup_union_Some_r'|].
    iNext; iIntros "Hh".
    iDestruct (big_sepM_lookup _ _ l v with "Hlow") as "#Hv"; first done.
    iDestruct (hinv_intro with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha"; first by eauto.
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma wp_store p E l v' e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Store (Loc l) e @ p; E
    {{{ RET UnitV; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx mapsto_eq /mapsto_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_high_included h h' l 1 v') => // ??.
    iApply (wp_store_pst with "Hh"); [done|exact: lookup_union_Some_l|].
    iNext; iIntros "Hh". iDestruct (hinv_high with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha"; last by iApply "HΦ".
    iFrame. iPureIntro. exact: to_heap_store_high.
  Qed.

  Lemma wp_store_low p E l e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low  l ∗ ▷ low  v }}} Store (Loc l) e @ p; E
    {{{ RET UnitV; True }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "(#Hinv&>Hl&Hv) HΦ".
    rewrite /heap_ctx low_loc lowloc'_eq /lowloc'_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v' ?].
    iApply (wp_store_pst with "Hh"); [done|exact: lookup_union_Some_r'|].
    iNext; iIntros "Hh".
    iDestruct (hinv_store_low with "Hh Hlow Hv") as "Hh"; try done.
    iMod ("Hcl" with "* [Hh]") as "Ha"; last by iApply "HΦ".
    iFrame. by erewrite to_heap_low_insert_override.
  Qed.

  Lemma wp_cas_fail p E l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v' }}} CAS (Loc l) e1 e2 @ p; E
    {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx mapsto_eq /mapsto_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_high_included h h' l q v') => // ??.
    iApply (wp_cas_fail_pst with "Hh");
      [done|exact: lookup_union_Some_l|done|].
    iNext; iIntros "Hh". iDestruct (hinv_intro with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc p E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v1 }}} CAS (Loc l) e1 e2 @ p; E
    {{{ RET LitV (LitBool true); l ↦ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx mapsto_eq /mapsto_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_high_included h h' l 1 v1) => // ??.
    iApply (wp_cas_suc_pst with "Hh");
      [done|exact: lookup_union_Some_l|].
    iNext; iIntros "Hh". iDestruct (hinv_high with "Hh Hlow") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Ha"; last by iApply "HΦ".
    iFrame. iPureIntro. exact: to_heap_store_high.
  Qed.

  Lemma wp_cas_low p E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low l ∗ ▷ low v2 }}} CAS (Loc l) e1 e2 @ p; E
    {{{ b, RET LitV (LitBool b); True }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "(#Hinv&>Hl&Hv) HΦ".
    rewrite /heap_ctx low_loc lowloc'_eq /lowloc'_def.
    iMod (auth_open_strong with "[$Hinv $Hl]")
      as ([h h']) "(%&%&[Hh Hlow]&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v' ?].
    case: (decide (v' = v1)) => [<-|?].
    - iApply (wp_cas_suc_pst with "Hh");
        [done|exact: lookup_union_Some_r'|].
      iNext; iIntros "Hh".
      iDestruct (hinv_store_low with "Hh Hlow Hv") as "Hh"; try done.
      iMod ("Hcl" with "* [Hh]") as "Ha"; last by iApply "HΦ".
      iFrame. by erewrite to_heap_low_insert_override.
    - iApply (wp_cas_fail_pst with "Hh");
        [done|exact: lookup_union_Some_r'|done|].
      iNext; iIntros "Hh". iDestruct (hinv_intro with "Hh Hlow") as "Hh".
      iMod ("Hcl" with "* [Hh]") as "Ha"; first by eauto. by iApply "HΦ".
  Qed.
End heap.
