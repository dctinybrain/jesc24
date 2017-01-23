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
  Definition lowloc_def l : iProp Σ := auth_own γ {[l := Lval]}.
  Definition lowloc_aux : { x | x = @lowloc_def }. by eexists. Qed.
  Definition lowloc := proj1_sig lowloc_aux.
  Definition lowloc_eq : @lowloc = @lowloc_def := proj2_sig lowloc_aux.

  (**
    Low values. When proving a function low, one may use any
    invariant.
  *)
  Definition lowval_pre (rec : val -c> iProp Σ) : val -c> iProp Σ := λ v,
    match v with
    | RecV f x e _ => □ ▷ ∀ v, rec v -∗
      WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ rec }}
    | LitV (LitLoc l) => lowloc l
    | LitV (LitInt _ | LitBool _ | LitUnit) => True
    | PairV v1 v2 => ▷(rec v1 ∗ rec v2)
    | InjLV v | InjRV v => ▷(rec v)
    end%I.

  Instance lowval_pre_contractive : Contractive lowval_pre.
  Proof.
    rewrite /lowval_pre=> n rec rec' Hrec ?.
    repeat (f_contractive || f_equiv); apply Hrec.
  Qed.

  Definition lowval_def : val → iProp Σ := fixpoint lowval_pre.
  Definition lowval_aux : { x | x = @lowval_def }. by eexists. Qed.
  Definition lowval := proj1_sig lowval_aux.
  Definition lowval_eq : @lowval = @lowval_def := proj2_sig lowval_aux.

  Lemma lowval_unfold v : lowval v ≡ lowval_pre lowval v.
  Proof. rewrite lowval_eq. apply (fixpoint_unfold lowval_pre). Qed.

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
Typeclasses Opaque mapsto lowloc lowval.
Instance: Params (@mapsto) 2.
Instance: Params (@lowloc) 2.
Instance: Params (@lowval) 3.
Instance: Params (@heap_ctx') 3.

Notation "l ↦{ q } v" := (mapsto heap_name l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (mapsto heap_name l 1 v) (at level 20) : uPred_scope.

Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

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
  low_persistent a :> PersistentP (low a)
}.
Arguments Low {_ _} _ _.
Arguments low {_ _ _} _ : simpl never.
Instance: Params (@low) 3.

Section low.
  Context `{heapG Σ}.

  (** Low locations are defined by [lowloc]. *)
  Global Instance lowloc_persistent l : PersistentP (lowloc heap_name l).
  Proof. rewrite lowloc_eq /lowloc_def. apply _. Qed.
  Global Instance loc_low : LowIntegrity Σ loc := Low (lowloc heap_name) _.
  Global Instance loc_low_timeless (l : loc) : TimelessP (low l).
  Proof. rewrite /low/= lowloc_eq /lowloc_def. apply _. Qed.

  Lemma low_loc l : low l ⊣⊢ lowloc heap_name l.
  Proof. by []. Qed.

  (** Literals other than locations are automatically low. *)
  Definition lowlit : base_lit → iProp Σ :=
    λ lit, match lit with
    | LitInt _ | LitBool _ | LitUnit => True
    | LitLoc l => low l
    end%I.
  Global Instance lowlit_persistent lit : PersistentP (lowlit lit).
  Proof. case: lit; apply _. Qed.
  Global Instance lit_low : LowIntegrity Σ base_lit := Low lowlit _.
  Global Instance lit_low_timeless (lit : base_lit) : TimelessP (low lit).
  Proof. case: lit; apply _. Qed.

  Lemma low_lit lit :
    low lit ⊣⊢
    match lit with
    | LitInt _ | LitBool _ | LitUnit => True
    | LitLoc l => low l
    end.
  Proof. by []. Qed.

  (**
    A (syntactically) low expression contains neither assertions nor
    high locations. (We reserve assertions for verified code.)
  *)
  Definition lowexpr : expr → iProp Σ :=
    fix rec e := match e with
    | Var _ => True
    | Assert _ => False
    | Lit lit => low lit
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
  Global Instance lowexpr_low : LowIntegrity Σ expr := Low lowexpr _.
  Global Instance lowexpr_low_timeless (e : expr) : TimelessP (low e).
  Proof.
    rewrite/lowexpr; elim: e=>//; rewrite-/lowexpr; by apply _.
  Qed.

  Lemma low_expr e :
    low e ⊣⊢
    match e with
    | Var _ => True
    | Assert _ => False
    | Lit lit => low lit
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e | InjR e
    | Fork e | Alloc e | Load e
      => low e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 => low e1 ∗ low e2
    | If e1 e2 e3 | Case e1 e2 e3 | CAS e1 e2 e3
      => low e1 ∗ low e2 ∗ low e3
    end.
  Proof. by case: e. Qed.

  (** Low values are defined by [lowval]. *)
  Global Instance lowval_persistent v : PersistentP (lowval heap_name v).
  Proof.
    iIntros "Hv". iLöb as "IH" forall (v). rewrite lowval_unfold /lowval_pre.
    destruct v.
    - by iDestruct "Hv" as "#Hv".
    - by iDestruct "Hv" as "#Hv".
    - rewrite always_later. iNext. iDestruct "Hv" as "(Hv1&Hv2)".
      iDestruct ("IH" with "* Hv1") as "#Hv1'".
      iDestruct ("IH" with "* Hv2") as "#Hv2'". iClear "Hv1 Hv2".
      iAlways. by iFrame "#".
    - rewrite always_later. iNext. by iSpecialize ("IH" with "* Hv").
    - rewrite always_later. iNext. by iSpecialize ("IH" with "* Hv").
  Qed.
  Global Instance val_low : LowIntegrity Σ val := Low (lowval heap_name) _.

  Lemma lowval_low v : low v ⊣⊢ lowval heap_name v.
  Proof. by []. Qed.

  Lemma low_val v :
    low v ⊣⊢
    match v with
    | RecV f x e _ => □ ▷ ∀ v, low v -∗
      WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ low }}
    | LitV lit => low lit
    | PairV v1 v2 => ▷ (low v1 ∗ low v2)
    | InjLV v | InjRV v => ▷ low v
    end.
  Proof. by destruct v; rewrite lowval_low lowval_unfold. Qed.

  Lemma low_rec f x e `{!Closed (f :b: x :b: []) e} :
    low (RecV f x e) ⊣⊢
    □ ▷ ∀ v Φ, low v -∗ (∀ v, low v -∗ Φ v) -∗
    WP subst' x (of_val v) (subst' f (Rec f x e) e) ?{{ Φ }}.
  Proof.
    rewrite low_val. iSplit.
    - iIntros "#Hv !#". iNext. iIntros (v2 Φ) "#Hv2 HΦ".
      iApply (wp_wand with "[Hv Hv2] [$HΦ]"). by iApply ("Hv" with "[$Hv2]").
    - iIntros "#Hv !#". iNext. iIntros (v2) "#Hv2".
      iApply ("Hv" with "[$Hv2] []"). by iIntros.
  Qed.

  Global Instance val_low_lit_timeless lit : TimelessP (low (LitV lit)).
  Proof. by rewrite /TimelessP low_val lit_low_timeless. Qed.
(* Also sound, but who cares?
  Global Instance low_rec_except_0 f x e `{!Closed (f :b: x :b: []) e} :
    IsExcept0 (low (RecV f x e)).
  Global Instance low_pair_except_0 v1 v2 : IsExcept0 (low (PairV v1 v2)).
  Global Instance low_inj_l_except_0 v : IsExcept0 (low (InjLV v)).
  Global Instance low_inj_r_except_0 v : IsExcept0 (low (InjRV v)).
*)
End low.

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
    by rewrite mapsto_eq low_loc lowloc_eq
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
    - by rewrite low_loc lowloc_eq /lowloc_def.
  Qed.

  (** Heap rules for high and low locations. *)
  Lemma wp_alloc p E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx }}} Alloc e @ p; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
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
    {{{ l, RET LitV (LitLoc l); low l }}}.
  Proof.
    iIntros (?? Φ) "[#Hinv Hv] HΦ". rewrite -wp_fupd.
    iApply (wp_alloc with "Hinv"); eauto.
    iNext. iIntros (l) "Hl". rewrite [(l ↦ v)%I]later_intro [low _]later_intro.
    iDestruct (heap_mark_low with "Hinv Hl Hv") as "Hl"; first done.
    by iApply ("HΦ" with "Hl").
  Qed.

  Lemma wp_load p E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ p; E
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
    {{{ heap_ctx ∗ ▷ low l }}} Load (Lit (LitLoc l)) @ p; E
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx low_loc lowloc_eq /lowloc_def.
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
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ p; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
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
    {{{ heap_ctx ∗ ▷ low  l ∗ ▷ low  v }}} Store (Lit (LitLoc l)) e @ p; E
    {{{ RET LitV LitUnit; True }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "(#Hinv&>Hl&Hv) HΦ".
    rewrite /heap_ctx low_loc lowloc_eq /lowloc_def.
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
    {{{ heap_ctx ∗ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ p; E
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
    {{{ heap_ctx ∗ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ p; E
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
    {{{ heap_ctx ∗ ▷ low l ∗ ▷ low v2 }}} CAS (Lit (LitLoc l)) e1 e2 @ p; E
    {{{ b, RET LitV (LitBool b); True }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "(#Hinv&>Hl&Hv) HΦ".
    rewrite /heap_ctx low_loc lowloc_eq /lowloc_def.
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
