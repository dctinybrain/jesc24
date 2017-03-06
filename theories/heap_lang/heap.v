From iris.prelude Require Import gmultiset.
From iris.algebra Require Import auth gmap coPset csum agree.
From iris.algebra Require Export gset frac.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import own auth fractional.
From iris.base_logic Require Import big_op.
From iris.heap_lang Require addenda.
From iris.heap_lang Require Export on_val lifting.
From iris.proofmode Require Import tactics.
Import uPred.
Import addenda.fin_maps.
Import addenda.option addenda.gmap addenda.csum.
Import addenda.lib_auth addenda.algebra_auth.

Local Hint Resolve to_of_val.

(** The CMRAs we need. *)
Local Notation heap := (gmap loc val).
Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT :=
  gmapUR loc (csumR (prodR fracR (agreeR valC)) unitR).
Local Notation Hval q v := (Cinl (q%Qp, to_agree v)).
Local Notation Lval := (Cinr ()).
Local Notation locset := (gsetUR loc).

Class heapG Σ := HeapG {
  heap_ownP_inG :> ownPG heap_lang Σ;
  heap_liveG_inG :> inG Σ (authR locset);
  heap_inG :> authG Σ heapUR;
  heap_name : gname * gname
}.

Class heapPreG Σ := HeapPreG {
  heap_preG_ownP_inG : ownPPreG heap_lang Σ;
  heap_preG_liveG_inG : inG Σ (authR locset);
  heap_preG_inG : authG Σ heapUR
}.
(*
 * Lower priority than heapG's instances so the occurrence of
 * [heap_ctx] in the statement of [heap_adequacy] refers to the
 * "inner" [heapG] rather than the "outer" [heapPreG].
 *)
Existing Instance heap_preG_ownP_inG | 30.
Existing Instance heap_preG_liveG_inG | 30.
Existing Instance heap_preG_inG | 30.

Definition heapΣ : gFunctors := #[
  ownPΣ state; GFunctor (constRF (authR locset)); authΣ heapUR
].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [?[??]%subG_inv]%subG_inv. constructor; apply _. Qed.

(** * Heap resources and invariant *)
Section definitions.
  Context `{ownPG heap_lang Σ, inG Σ (authR locset), authG Σ heapUR}.
  Context (γ : gname * gname).
  Implicit Types l : loc.
  Implicit Types q : Qp.
  Implicit Types v : val.
  Implicit Types h : heap.

  (** Live locations. *)
  Definition liveloc'_def l : iProp Σ := own (γ.2) (◯ (to_gset {[ l ]})).
  Definition liveloc'_aux : { x | x = @liveloc'_def }. by eexists. Qed.
  Definition liveloc' := proj1_sig liveloc'_aux.
  Definition liveloc'_eq : @liveloc' = @liveloc'_def := proj2_sig liveloc'_aux.

  (** High locations. *)
  Definition mapsto_def l q v : iProp Σ :=
    (auth_own (γ.1) {[l := Hval q v]} ∗ liveloc' l)%I.
  Definition mapsto_aux : { x | x = @mapsto_def }. by eexists. Qed.
  Definition mapsto := proj1_sig mapsto_aux.
  Definition mapsto_eq : @mapsto = @mapsto_def := proj2_sig mapsto_aux.

  (** Low locations. *)
  Definition lowloc'_def l : iProp Σ :=
    (auth_own (γ.1) {[l := Lval]} ∗ liveloc' l)%I.
  Definition lowloc'_aux : { x | x = @lowloc'_def }. by eexists. Qed.
  Definition lowloc' := proj1_sig lowloc'_aux.
  Definition lowloc'_eq : @lowloc' = @lowloc'_def := proj2_sig lowloc'_aux.

  (** Low values. *)
  Notation lowval' := (on_val lowloc').

  (**
    Invariant: The state is good and maps every high location to its
    value and every low location to a low value. Locations are live
    when they're in the heap's domain.
  *)
  Definition to_high : heap → heapUR := fmap (λ v, Hval 1 v).
  Definition to_low : heap → heapUR  := fmap (λ _, Lval).
  Definition to_heap (a : heap * heap) : heapUR :=
    let: (h, h') := a in to_high h ⋅ to_low h'.
  Definition hinv' (a : heap * heap) : iProp Σ := (
    let: (h, h') := a in
    ownP (good_state (h ∪ h'))
    ∗ ([∗ map] v ∈ h', lowval' v)
    ∗ own (γ.2) (● (dom (gset loc) (h ∪ h')))
  )%I.

  Lemma hinv_alloc h :
    ownP (good_state h) ∗ own (γ.2) (● dom (gset loc) h) ⊢ ▷ hinv' (h, ∅).
  Proof.
    rewrite /hinv' right_id big_sepM_empty left_id. exact: later_intro.
  Qed.

  Lemma to_heap_valid h : ✓ to_heap (h, ∅).
  Proof. move=>l. rewrite lookup_op !lookup_fmap. by case (h !! l). Qed.

  Definition heap_ctx' : iProp Σ := auth_ctx (γ.1) heapN to_heap hinv'.

  Global Instance heap_ctx'_persistent : PersistentP heap_ctx'.
  Proof. apply _. Qed.
End definitions.

Notation liveloc := (liveloc' heap_name).

Notation "l ↦{ q } v" := (mapsto heap_name l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (mapsto heap_name l 1 v) (at level 20) : uPred_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Notation lowloc := (lowloc' heap_name).
Notation lowval := (on_val lowloc).
Notation heap_ctx := (heap_ctx' heap_name).
Local Notation hinv := (hinv' heap_name).

(** Allocating the invariant. *)
(** We cannot use [auth_alloc] as [hinv] depends on the ghost names. *)
Lemma heap_ctx_alloc `{ownPG heap_lang Σ, inG Σ (authR locset), authG Σ heapUR} E h :
  ownP (good_state h) ={E}=∗ ∃ γ, heap_ctx' γ.
Proof.
  iIntros "Hσ". set h' := to_heap (h, ∅). set X := dom (gset loc) h.
  iMod (own_alloc (Auth (Excl' h') h')) as (γheap) "Ha".
  { split. done. exact: to_heap_valid. }
  iMod (own_alloc (Auth (Excl' X) X)) as (γlive) "Hlive"; first done.
  set γ := (γheap, γlive). set hinv_γ := @hinv' _ _ _ _ γ.
  rewrite (auth_both_op h') (auth_both_op X).
  iDestruct "Ha" as "[Ha _]". iDestruct "Hlive" as "[Hlive _]".
  iDestruct (@hinv_alloc _ _ _ _ γ with "[$Hσ $Hlive]") as "Hh".
  iMod (inv_alloc heapN _ (auth_inv γheap to_heap hinv_γ) with "[-]") as "#?".
  { iNext. rewrite/auth_inv. iExists (h, ∅). by iFrame. }
  iModIntro. iExists γ. by rewrite/heap_ctx'/auth_ctx.
Qed.

(** Observing good states. *)
Lemma heap_ctx_is_good `{heapG Σ} E :
 ↑heapN ⊆ E → heap_ctx ={E,∅}=∗ ∃ σ, ownP σ ∧ ⌜is_good σ⌝.
Proof.
  iIntros (?) "Hh". iMod (fupd_intro_mask' _ (↑heapN)) as "_"; first done.
  iMod (auth_empty (heap_name.1)) as "Ha".
  iMod (auth_open with "[$Hh $Ha]") as ([h h']) "(_&[>Hh _]&_)";
    first done.
  iExists _; iFrame. by rewrite subseteq_empty_difference_L.
Qed.

(** Live locations *)
Section live.
  Context `{heapG Σ}.

  Definition live : gset loc → iProp Σ := λ X, ([∗ set] l ∈ X, liveloc l)%I.

  Global Instance liveloc_persistent l : PersistentP (liveloc l).
  Proof. rewrite liveloc'_eq. apply _. Qed.
  Global Instance liveloc_timeless l : TimelessP (liveloc l).
  Proof. rewrite liveloc'_eq. apply _. Qed.

  Global Instance live_persistent X : PersistentP (live X).
  Proof. apply _. Qed.
  Global Instance live_timeless X : TimelessP (live X).
  Proof. apply _. Qed.

  Lemma lowloc_live l : lowloc l ⊢ liveloc l.
  Proof. by rewrite lowloc'_eq /lowloc'_def sep_elim_r. Qed.

  Lemma mapsto_live l q v : l ↦{q} v ⊢ liveloc l.
  Proof. by rewrite mapsto_eq /mapsto_def sep_elim_r. Qed.
End live.

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

Section low.
  Context `{heapG Σ}.

  (**
    Locations start off high and may be marked low by the
    (irreversible) ghost move [heap_mark_low].
  *)
  Global Instance lowloc_persistent l : PersistentP (lowloc l).
  Proof. rewrite lowloc'_eq. apply _. Qed.
  Global Instance lowloc_timeless l : TimelessP (lowloc l).
  Proof. rewrite lowloc'_eq. apply _. Qed.
  Global Instance loc_low : LowIntegrity Σ loc := Low lowloc _ _.
  Global Instance loc_low_timeless (l : loc) : TimelessP (low l).
  Proof. rewrite /low/=. apply _. Qed.

  Lemma low_loc l : low l ⊣⊢ lowloc l. Proof. by []. Qed.

  Lemma low_live l : low l ⊢ liveloc l.
  Proof. by rewrite low_loc lowloc_live. Qed.

  (** Low values lift low locations to values. *)
  Global Instance val_low : LowIntegrity Σ val := Low lowval _ _.

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
Module internal.

Notation Live h := (own (heap_name.2) (● dom (gset loc) h)) (only parsing).
Notation HighLoc l q v := (auth_own (heap_name.1) {[l := Hval q v]})
  (only parsing).
Notation LowLoc l := (auth_own (heap_name.1) {[l := Lval ]}) (only parsing).
Notation Phys h := (ownP (good_state h)) (only parsing).
Notation Low h' := ([∗ map] v' ∈ h', low v')%I (only parsing).

Section internal.
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

  Lemma high_eq l q v : l ↦{q} v ⊣⊢ HighLoc l q v ∗ liveloc l.
  Proof. by rewrite mapsto_eq. Qed.

  Lemma high_HighLoc l q v : l ↦{q} v ⊢ HighLoc l q v.
  Proof. by rewrite high_eq sep_elim_l. Qed.

  Lemma low_eq l : low l ⊣⊢ LowLoc l ∗ liveloc l.
  Proof. by rewrite low_loc lowloc'_eq. Qed.

  Lemma hinv_mark_low h h' l v :
    ✓ to_heap (h, h') → {[l := Hval 1 v]} ≼ to_heap (h, h') →
    ▷ low v -∗ ▷ Phys (h ∪ h') -∗ ▷ Low h' -∗ ▷ Live (h ∪ h') -∗
    ▷ hinv (delete l h, <[l:=v]> h').
  Proof.
    move=>Hv /to_heap_high_included -/(_ Hv)[??]. rewrite/hinv.
    iIntros "Hv Hσ Hlow Hlive". rewrite -delete_insert_union //.
    iFrame. rewrite 2!big_sepM_later big_sepM_insert //. by iFrame.
  Qed.

  (* PDS: Hoist. *)
  Lemma to_gset_singleton l : to_gset {[l]} = {[l]}.
  Proof.
    apply mapset_eq=> x. rewrite elem_of_to_gset; last exact: singleton_finite.
    by rewrite 2!elem_of_singleton.
  Qed.

  Lemma live_obs h l X :
    h !! l = None →
    Live h -∗ live X -∗ ⌜l ∉ X⌝.
  Proof.
    rewrite/live liveloc'_eq /liveloc'_def=>Hdom.
    induction X as [|x X Hx IH] using collection_ind_L.
    { iIntros "Hh _". iPureIntro. exact: not_elem_of_empty. }
    iIntros "Hh HX".
    rewrite big_sepS_union; last by move=>?/elem_of_singleton->.
    rewrite big_sepS_singleton. iDestruct "HX" as "(Hx & HX)".
    iDestruct (IH with "Hh HX") as "%". rewrite not_elem_of_union.
    case: (decide (l = x))=>?; last first.
    { iFrame. iPureIntro. by rewrite not_elem_of_singleton. }
    subst. iExFalso. iDestruct (own_valid_2 with "Hh Hx") as "Hv".
    iDestruct "Hv" as %[Hinc%gset_included _]%auth_valid_discrete_2.
    iPureIntro. move: Hinc=>/(_ x).
    rewrite (to_gset_singleton x) elem_of_singleton=>
      /(_ (eq_refl _))/elem_of_dom.
    by rewrite Hdom=>-[].
  Qed.

  Lemma live_alloc h l v :
    Live h ==∗ Live (<[l:=v]> h) ∗ liveloc l.
  Proof.
    rewrite/live liveloc'_eq /liveloc'_def.
    rewrite -(sep_elim_r (own (heap_name.2) (◯ dom (gset loc) h))
      (own _ (◯ to_gset {[l]}))) -2!own_op -auth_frag_op.
    apply own_update, auth_update_alloc.
    rewrite dom_insert comm gset_op_union (to_gset_singleton l).
    apply gset_local_update, union_subseteq_l.
  Qed.

  Lemma hinv_high h h' l v :
    Phys (<[l:=v]> (h ∪ h')) -∗ Low h' -∗ Live (<[l:=v]> (h ∪ h')) -∗
    hinv (<[l:=v]> h, h').
  Proof. rewrite/hinv insert_union_l. by iIntros; iFrame. Qed.

  Lemma hinv_intro h h' :
    Phys (h ∪ h') -∗ Low h' -∗ Live (h ∪ h') -∗ hinv (h, h').
  Proof. rewrite/hinv. by iIntros; iFrame. Qed.

  Lemma to_heap_alloc_high h h' l v :
    (h ∪ h') !! l = None →
    (to_heap (h, h'), ∅) ~l~> (to_heap (<[l:=v]> h, h'), {[l := Hval 1 v]}).
  Proof.
    move=>Hdom.
    rewrite to_heap_high_insert; last by move: Hdom=>/lookup_union_None[].
    apply alloc_singleton_local_update; last done.
    by apply lookup_to_heap_None.
  Qed.

  Lemma live_store_high h h' l v' v :
    h !! l = Some v' → h' !! l = None →
    Live (h ∪ h') ⊣⊢ Live (<[l:=v]> (h ∪ h')).
  Proof.
    move=>??. do 4!f_equiv. apply mapset_eq=>x. rewrite 2!elem_of_dom.
    case: (decide (x = l))=>?.
    - subst. simplify_map_eq. by rewrite 2!is_Some_alt.
    - by rewrite lookup_insert_ne.
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

  Lemma live_store_low h h' l v1 v2 :
    h !! l = None → h' !! l = Some v1 →
    Live (h ∪ h') ⊣⊢ Live (h ∪ <[l:=v2]> h').
  Proof.
    move=>Hhigh Hlow.
    do 4!f_equiv. apply mapset_eq=>x. rewrite 2!elem_of_dom.
    case: (decide (x = l))=>?.
    - subst. rewrite (lookup_union_Some_r' _ _ _ v1) //.
      rewrite (lookup_union_Some_r' _ _ _ v2) //.
      by rewrite 2!is_Some_alt.  by rewrite lookup_insert.
    - case Hleft: (h !! x) => [v|]; first by simplify_map_eq.
      case Hright: (h' !! x) => [v'|].
      + do 2!rewrite (lookup_union_Some_r' _ _ _ v') //.
        by rewrite lookup_insert_ne.
      + have->: (h ∪ h') !! x = None by apply lookup_union_None.
        have->: (h ∪ <[l:=v2]> h') !! x = None; last done.
        apply lookup_union_None. by rewrite lookup_insert_ne.
  Qed.

  Lemma hinv_store_low h h' l v1 v2 :
    h !! l = None → h' !! l = Some v1 →
    low v2 -∗ Phys (<[l:=v2]> (h ∪ h')) -∗ Low h' -∗ Live (h ∪ <[l:=v2]> h') -∗
    hinv (h, <[l:=v2]> h').
  Proof.
    move=>??.
    rewrite /hinv insert_union_r // big_sepM_insert_override_2 //.
    iIntros "? ? Hlow ?". iFrame. iApply "Hlow". eauto.
  Qed.
End internal.
End internal.

(** * Heap interface *)
Section heap.
  Context `{heapG Σ}.
  Implicit Types l : loc.
  Implicit Types q : Qp.
  Implicit Types v : val.
  Implicit Types h : heap.
  Import internal.

  (** ** Structure *)
  (**
	High locations and the heap context enjoy their usual
	properties. Low locations are timeless, persistent, and
	disjoint from high locations. High locations containing low
	values can be marked low.
  *)
  Lemma high_not_low l q v : l ↦{q} v ∗ low l ⊢ False.
  Proof.
    rewrite high_HighLoc low_eq (sep_elim_l _ (liveloc _)).
    rewrite -auth_own_op auth_own_valid discrete_valid.
    by rewrite op_singleton singleton_valid.
  Qed.

  Global Instance mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite mapsto_eq. apply _. Qed.
  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    enough (F : Fractional (λ q, HighLoc l q v)).
    { intros p q. rewrite 3!high_eq. iSplit.
      - iIntros "(Hpq & #HL)". iFrame "HL HL". by rewrite -F.
      - iIntros "([Hp _] & Hq & HL)". rewrite (F p q). by iFrame "Hp Hq HL". }
    intros p q. rewrite -auth_own_op.
    by rewrite op_singleton Cinl_op pair_op agree_idemp.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite 2!high_HighLoc -auth_own_op auth_own_valid.
    rewrite discrete_valid op_singleton singleton_valid Cinl_op pair_op.
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
    rewrite high_HighLoc auth_own_valid 2!discrete_valid singleton_valid.
    by apply pure_mono=> -[].
  Qed.
  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "[H1 H2]". iDestruct (mapsto_agree with "[$H1 $H2]") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.

  Lemma heap_mark_low E l v :
    ↑heapN ⊆ E →
    heap_ctx -∗ ▷ l ↦ v -∗ ▷ low v ={E}=∗ low l.
  Proof.
    rewrite high_eq. iIntros (?) "Hh >(Hl & HL) Hv".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ&Hlow&Hlive)&Hcl)"; first done.
    iDestruct (hinv_mark_low with "Hv Hσ Hlow Hlive") as "Hh"=>//.
    iMod ("Hcl" with "* [Hh]") as "Hl".
    - iFrame. iPureIntro. exact: to_heap_mark_low.
    - rewrite low_eq. by iFrame.
  Qed.

  (** ** Operational rules *)

  Lemma wp_alloc_live p E e v X :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ live X }}} Alloc e @ p; E
    {{{ l, RET LocV l; l ↦ v ∗ ⌜l ∉ X⌝ }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "(Hh&#HX) HΦ". rewrite /heap_ctx.
    iMod (auth_empty (heap_name.1)) as "Ha".
    iMod (auth_open with "[$Hh $Ha]")
      as ([h h']) "(%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    iApply (wp_alloc_big with "Hσ"); first done. iNext. iIntros (l) "[% Hσ]".
    iDestruct (live_obs _ l X with "Hlive HX") as "#HXl"; first done.
    iMod (live_alloc _ l v with "Hlive") as "(Hlive & HL)".
    iDestruct (hinv_high with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Hl".
    - iFrame. iPureIntro. exact: to_heap_alloc_high.
    - iApply "HΦ". rewrite high_eq. by iFrame.
  Qed.

  Lemma wp_load p E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Load (Loc l) @ p; E
    {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (? Φ) "[Hh >Hl] HΦ". rewrite high_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_high_included h h' l q v) => // ??.
    iApply (wp_load_big with "Hσ"); [done|exact: lookup_union_Some_l|].
    iNext. iIntros "Hσ". iDestruct (hinv_intro with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Hl"; first by eauto.
    by iApply ("HΦ" with "[$Hl $HL]").
  Qed.

  Lemma wp_load_low p E l :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low l }}} Load (Loc l) @ p; E
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "[Hh >Hl] HΦ". rewrite low_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v ?].
    iApply (wp_load_big with "Hσ"); [done|exact: lookup_union_Some_r'|].
    iNext. iIntros "Hσ".
    iDestruct (big_sepM_lookup _ _ l v with "Hlow") as "#Hv"; first done.
    iDestruct (hinv_intro with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "_"; first by eauto.
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma wp_store p E l v' e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Store (Loc l) e @ p; E
    {{{ RET UnitV; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "[Hh >Hl] HΦ".
    rewrite high_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_high_included h h' l 1 v') => // ??.
    iApply (wp_store_big with "Hσ"); [done|exact: lookup_union_Some_l|].
    iDestruct (live_store_high _ _ l _ v with "Hlive") as "Hlive"=>//.
    iNext. iIntros "Hσ". iDestruct (hinv_high with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Hl".
    - iFrame. iPureIntro. exact: to_heap_store_high.
    - rewrite high_eq. by iApply ("HΦ" with "[$Hl $HL]").
  Qed.

  Lemma wp_store_low p E l e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low  l ∗ ▷ low  v }}} Store (Loc l) e @ p; E
    {{{ RET UnitV; True }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "(Hh&>Hl&Hv) HΦ".
    rewrite low_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v' ?].
    iApply (wp_store_big with "Hσ"); [done|exact: lookup_union_Some_r'|].
    iDestruct (live_store_low _ _ _ _ v with "Hlive") as "Hlive"=>//.
    iNext. iIntros "Hσ".
    iDestruct (hinv_store_low with "Hv Hσ Hlow Hlive") as "Hh"; try done.
    iMod ("Hcl" with "* [Hh]") as "_"; last by iApply "HΦ".
    iFrame. by erewrite to_heap_low_insert_override.
  Qed.

  Lemma wp_cas_fail p E l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v' }}} CAS (Loc l) e1 e2 @ p; E
    {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?? Φ) "[Hh >Hl] HΦ".
    rewrite high_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_high_included h h' l q v') => // ??.
    iApply (wp_cas_fail_big with "Hσ");
      [done|exact: lookup_union_Some_l|done|].
    iNext. iIntros "Hσ". iDestruct (hinv_intro with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Hl".
    by eauto. by iApply ("HΦ" with "[$Hl $HL]").
  Qed.

  Lemma wp_cas_suc p E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v1 }}} CAS (Loc l) e1 e2 @ p; E
    {{{ RET LitV (LitBool true); l ↦ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "[Hh >Hl] HΦ".
    rewrite high_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_high_included h h' l 1 v1) => // ??.
    iDestruct (live_store_high _ _ l _ v2 with "Hlive") as "Hlive"=>//.
    iApply (wp_cas_suc_big with "Hσ");
      [done|exact: lookup_union_Some_l|].
    iNext. iIntros "Hσ". iDestruct (hinv_high with "Hσ Hlow Hlive") as "Hh".
    iMod ("Hcl" with "* [Hh]") as "Hl".
    - iFrame. iPureIntro. exact: to_heap_store_high.
    - rewrite high_eq. by iApply ("HΦ" with "[$Hl $HL]").
  Qed.

  Lemma wp_cas_low p E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low l ∗ ▷ low v2 }}} CAS (Loc l) e1 e2 @ p; E
    {{{ b, RET LitV (LitBool b); True }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "(Hh&>Hl&Hv) HΦ".
    rewrite low_eq. iDestruct "Hl" as "[Hl HL]".
    iMod (auth_open_strong with "[$Hh $Hl]")
      as ([h h']) "(%&%&(Hσ & Hlow & Hlive)&Hcl)"; first done.
    case: (to_heap_low_included h h' l) => // ? [v' ?].
    case: (decide (v' = v1)) => [<-|?].
    - iApply (wp_cas_suc_big with "Hσ");
        [done|exact: lookup_union_Some_r'|].
      iNext. iIntros "Hσ".
      iDestruct (live_store_low _ _ _ _ v2 with "Hlive") as "Hlive"=>//.
      iDestruct (hinv_store_low with "Hv Hσ Hlow Hlive") as "Hh"; try done.
      iMod ("Hcl" with "* [Hh]") as "_"; last by iApply "HΦ".
      iFrame. by erewrite to_heap_low_insert_override.
    - iApply (wp_cas_fail_big with "Hσ");
        [done|exact: lookup_union_Some_r'|done|].
      iNext. iIntros "Hσ". iDestruct (hinv_intro with "Hσ Hlow Hlive") as "Hh".
      iMod ("Hcl" with "* [Hh]") as "_". by eauto. by iApply "HΦ".
  Qed.
End heap.
Typeclasses Opaque liveloc' mapsto lowloc' heap_ctx'.

(** ** Derived rules *)
Section derived.
  Context `{heapG Σ}.
  Implicit Types e : expr.
  Implicit Types v : val.

  (**
	We can allocate high and low locations, observing
	freshness or not.
  *)
  Lemma wp_alloc p E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx }}} Alloc e @ p; E {{{ l, RET LocV l; l ↦ v }}}.
  Proof.
    iIntros (?? Φ) "Hh HΦ".
    iApply (wp_alloc_live _ _ _ _ ∅ with "[$Hh]"); eauto;
      first by rewrite /live big_sepS_empty.
    iNext. iIntros (l) "[Hl _]". by iApply "HΦ".
  Qed.

  Lemma wp_alloc_low_live p E e v X :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low v ∗ live X }}} Alloc e @ p; E
    {{{ l, RET LocV l; low l ∗ ⌜l ∉ X⌝ }}}.
  Proof.
    iIntros (?? Φ) "(#Hh & Hv & HX) HΦ". rewrite -wp_fupd.
    iApply (wp_alloc_live with "[$Hh $HX]"); eauto. iNext.
    iIntros (l) "(Hl & HX)". rewrite [(l ↦ v)%I]later_intro [low _]later_intro.
    iMod (heap_mark_low with "Hh Hl Hv") as "Hl"; first done.
    by iApply ("HΦ" with "[$Hl $HX]").
  Qed.

  Lemma wp_alloc_low p E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ low v }}} Alloc e @ p; E
    {{{ l, RET LocV l; low l }}}.
  Proof.
    iIntros (?? Φ) "(Hh & Hv) HΦ".
    iApply (wp_alloc_low_live _ _ _ _ ∅ with "[$Hh $Hv]"); eauto;
      first by rewrite /live big_sepS_empty.
    iNext. iIntros (l) "[Hl _]". by iApply "HΦ".
  Qed.

  (** We can always eliminate low values. *)
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
End derived.
