From iris.prelude Require Import countable decidable.
From iris.base_logic Require Import big_op.
From iris.heap_lang Require Export heap.
From iris.heap_lang Require Import addenda proofmode.
From iris.proofmode Require Import tactics.
Import addenda.list addenda.fin_maps.
Import uPred.

Local Hint Resolve to_of_val.

(** * Substitution of values for binders *)
Section substitution.
  Context `{heapG Σ}.
  Implicit Types e : expr.
  Implicit Types v : val.

  Definition encode_binder (x : binder) : positive :=
    encode (if x is BNamed x then Some x else None).
  Definition decode_binder (p : positive) : option binder :=
    if decode p is Some opt then
      Some (if opt is Some x then BNamed x else BAnon)
    else None.
  Lemma decode_encode_binder x :
    decode_binder (encode_binder x) = Some x.
  Proof.
    case: x=>[|x]. by naive_solver.
    by rewrite/encode_binder/decode_binder decode_encode.
  Qed.
  Instance binder_countable : Countable binder := {|
    encode := encode_binder; decode := decode_binder;
    decode_encode := decode_encode_binder
  |}.

  Definition env := gmap binder val.
  Implicit Types γ : env.

  Definition substitute_acc : binder * val → (expr → expr) → expr → expr :=
    λ xv f, let: (x, v) := xv in λ e, subst' x (of_val v) (f e).
  Definition substitute' : list (binder * val) → expr → expr :=
    foldr substitute_acc id.
  Definition substitute : env → expr → expr := substitute' ∘ map_to_list.
  Coercion substitute : env >-> Funclass.

  Lemma substitute'_cons x v L e :
    substitute' ((x, v) :: L) e = subst' x (of_val v) (substitute' L e).
  Proof. by []. Qed.

  Notation ext R := (pointwise_relation _ R).
  Instance substitute_acc_proper :
    Proper ((=) ==> ext (=) ==> ext (=)) substitute_acc.
  Proof.
    move=>[x v] [??] [<-<-] f1 f2 EQf e. by rewrite/substitute_acc (EQf e).
  Qed.

  Lemma substitute'_proper L1 L2 :
    (∀ x v v', (x, v) ∈ L1 → (x, v') ∈ L1 → v = v') →
    L1 ≡ₚ L2 →
    ext (=) (substitute' L1) (substitute' L2).
  Proof.
    rewrite/substitute'=>Hfun EQ. elim: EQ Hfun=> {L1 L2}.
    - done.
    - move=>[x v] L1' L2' EQ IH Hfun.
      do 2!rewrite foldr_cons. apply substitute_acc_proper, IH.
      done. by intros; eapply Hfun, elem_of_cons; right.
    - move=>[x v] [y v'] L Hfun e.
      do 4!rewrite foldr_cons. rewrite {1 2 4 5}/substitute_acc.
      case: (decide (x = y))=>?; last by rewrite subst_subst_ne'.
      subst. do 2!rewrite subst_subst'. do 2!f_equal.
      eapply Hfun; last by apply elem_of_cons; left.
      apply elem_of_cons. right. apply elem_of_cons. by left.
    - move=>L1 L L2 EQ1 IH1 EQ2 IH2 Hfun.
      rewrite (IH1 Hfun) (IH2 _)=> // x v v' ??.
      by eapply Hfun; eapply elem_of_list_permutation_proper.
  Qed.

  Lemma subst_substitute γ x v e :
    γ !! x = None → subst' x (of_val v) (γ e) = (<[x:=v]>γ) e.
  Proof.
    move=>?. rewrite /substitute/compose -substitute'_cons.
    symmetry. apply substitute'_proper.
    exact: map_to_list_unique. by rewrite map_to_list_insert.
  Qed.

  Lemma substitute_closed γ e : Closed [] e → γ e = e.
  Proof.
    move=>?. induction γ as [|x v γ Hx IH] using map_ind; first done.
    rewrite -subst_substitute // IH.
    case: x Hx=> //= x Hx. exact: subst_is_closed_nil.
  Qed.

  Lemma substitute_empty e : (∅ : env) e = e. Proof. by []. Qed.

  Lemma substitute_expr γ e :
    γ e =
    match e with
    | Var x => default (Var x) (γ !! BNamed x) of_val
    | Rec f x e => Rec f x $ (delete f $ delete x $ γ) e
    | App e1 e2 => App (γ e1) (γ e2)
    | Lit lit => e
    | UnOp op e => UnOp op (γ e)
    | BinOp op e1 e2 => BinOp op (γ e1) (γ e2)
    | If e1 e2 e3 => If (γ e1) (γ e2) (γ e3)
    | Pair e1 e2 => Pair (γ e1) (γ e2)
    | Fst e => Fst (γ e)
    | Snd e => Snd (γ e)
    | InjL e => InjL (γ e)
    | InjR e => InjR (γ e)
    | Case e1 e2 e3 => Case (γ e1) (γ e2) (γ e3)
    | Assert e => Assert (γ e)
    | Fork e => Fork (γ e)
    | Alloc e => Alloc (γ e)
    | Load e => Load (γ e)
    | Store e1 e2 => Store (γ e1) (γ e2)
    | CAS e1 e2 e3 => CAS (γ e1) (γ e2) (γ e3)
    end.
  Proof.
    move: γ e.
    have nullary: ∀ γ e, (∀ x es, subst x es e = e) → γ e = e.
    { move=>γ e Hf.
      have{Hf} Hf: ∀ x es, subst' x es e = e by case.
      induction γ as [|x v γ Hx IH] using map_ind; first done.
      by rewrite -subst_substitute // IH Hf. }
    Local Ltac by_induction γ Hf :=
      let IH := fresh "IH" in
      induction γ as [|x v γ Hx IH] using map_ind; first done;
      by rewrite -subst_substitute // IH Hf; f_equal; rewrite subst_substitute.
    have unary: ∀ f γ e, (∀ x es e, subst x es (f e) = f (subst x es e)) →
      γ (f e) = f (γ e).
    { move=>f γ e Hf.
      have{Hf} Hf: ∀ x es e, subst' x es (f e) = f (subst' x es e) by case.
      by_induction γ Hf. }
    have binary: ∀ f γ e1 e2,
      (∀ x es e1 e2, subst x es (f e1 e2) = f (subst x es e1) (subst x es e2)) →
      substitute γ (f e1 e2) = f (substitute γ e1) (substitute γ e2).
    { move=>f γ e1 e2 Hf.
      have{Hf} Hf: ∀ x es e1 e2, subst' x es (f e1 e2) =
         f (subst' x es e1) (subst' x es e2) by case.
      by_induction γ Hf. }
    have ternary: ∀ f γ e1 e2 e3,
      (∀ x es e1 e2 e3, subst x es (f e1 e2 e3) =
       f (subst x es e1) (subst x es e2) (subst x es e3)) →
      γ (f e1 e2 e3) = f (γ e1) (γ e2) (γ e3).
    { move=>f γ e1 e2 e3 Hf.
      have{Hf} Hf: ∀ x es e1 e2 e3, subst' x es (f e1 e2 e3) =
        f (subst' x es e1) (subst' x es e2) (subst' x es e3) by case.
      by_induction γ Hf. }
    move=>γ /= []; try by auto using nullary, unary, binary, ternary.
    - move=> x {nullary unary binary ternary}.
      induction γ as [|y v γ Hy IH] using map_ind; first done.
      rewrite -subst_substitute // IH {IH}. case: (decide (BNamed x = y)) => ?.
      { subst. by rewrite Hy lookup_insert /= /subst decide_True. }
      rewrite lookup_insert_ne //. destruct y as [|y]; first done.
      case: (_ !! _)=>[?|] =>/=.
      + rewrite subst_is_closed_nil //. exact: is_closed_of_val.
      + rewrite/subst decide_False // => ?. by subst.
    - move=>f x e {nullary unary binary ternary}.
      induction γ as [|y v γ Hy IH] using map_ind; first done.
      rewrite -subst_substitute // IH {IH}.
      case: (decide (y ≠ f ∧ y ≠ x))=>[[??]| /not_and_l EQ].
      { rewrite subst_rec_ne'; [| by left | by left]. f_equal.
        rewrite subst_substitute; last by do 2!rewrite lookup_delete_ne //.
        by do 2!rewrite delete_insert_ne //. }
      rewrite subst_rec'; last by case: EQ=>/dec_stable; [left| right; left].
      do 2!f_equal. case: EQ=>/dec_stable ?; subst.
      + by rewrite delete_commute [delete f _]delete_notin //
          delete_commute delete_insert //.
      + f_equal. by rewrite delete_notin // delete_insert //.
  Qed.
End substitution.

(** * The fundamental theorem of logical relations *)
(**
	We model adversarial values and closed, adversarial
	expressions with [low v] and [WP e ?{{ low }}], respectively
	(see [low_val]). Our aim is to show that, under the heap
	invariant, all syntactically low expressions (see [low_expr])
	inhabit the model.

	The proof is by induction on expressions. For the induction to
	go through, we must generalize to account for substitution of
	low values for variables. (Since the expression relation does
	not imply progress, these need not be closing substitutions.)
 *)
Section ftlr.

  Context `{heapG Σ}.
  Implicit Types γ : env.
  Implicit Types e : expr.
  Implicit Types v : val.

  Instance env_low : LowIntegrity Σ env := Low (λ γ, [∗ map] v ∈ γ, low v)%I _.

  Definition confined : expr → iProp Σ := λ e, (
    ∀ γ, heap_ctx -∗ low γ -∗ low e -∗ WP γ e ?{{ low }}
  )%I.

  Lemma low_env γ : low γ ⊣⊢ [∗ map] v ∈ γ, low v. Proof. by []. Qed.

  Lemma low_env_empty : low (∅ : env) ⊣⊢ True.
  Proof. exact: big_sepM_empty. Qed.

  Lemma low_env_insert γ x v :
    γ !! x = None → low v -∗ low γ -∗ low (<[x:=v]>γ).
  Proof.
    do 2!rewrite low_env. move=>?. rewrite big_sepM_insert //.
    iIntros. by iFrame "#".
  Qed.

  Lemma low_env_singleton x v : low ({[x:=v]} : env) ⊣⊢ low v.
  Proof. exact: big_sepM_singleton. Qed.

  Lemma low_env_lookup γ x v : γ !! x = Some v → low γ -∗ low v.
  Proof. exact: big_sepM_lookup. Qed.

  Lemma low_env_delete γ x  : low γ -∗ low (delete x γ).
  Proof.
    rewrite low_env. apply big_sepM_mono. exact: delete_subseteq. done.
  Qed.

  Lemma confined_alt e :
    confined e ⊣⊢
    ∀ γ Φ, heap_ctx -∗ low γ -∗ low e -∗ (∀ v, low v -∗ Φ v) -∗
    WP γ e ?{{ Φ }}.
  Proof.
    iSplit.
    - iIntros "Hc". iIntros (γ Φ) "Hh Hγ He". rewrite -wp_wand.
      by iApply ("Hc" with "[$Hh] [$Hγ] [$He]").
    - iIntros "Halt". iIntros (γ) "Hh Hγ He".
      iApply ("Halt" with "[$Hh] [$Hγ] [$He] []"). by iIntros.
  Qed.

  Lemma confined_var x : confined (Var x).
  Proof.
    iIntros (γ) "_ #Hγ _". rewrite substitute_expr.
    case Hdom: (_ !! _)=>[v|]/=; last by iApply wp_stuck_var.
    iApply wp_value'. by iApply (low_env_lookup with "[$Hγ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Var _)) => rewrite -confined_var.

  Lemma of_val_rec f x e `{!Closed (f :b: x :b: []) e} :
    Rec f x e = of_val (RecV f x e).
  Proof. symmetry. apply of_to_val. exact: to_val_rec. Qed.

  Lemma confined_rec f x e : □ confined e -∗ confined (Rec f x e).
  Proof.
    iIntros "#IHe". iIntros (γ) "#Hh #Hγ #He".
    rewrite low_expr substitute_expr. set erec := substitute _ _.
    case: (decide (Closed (f :b: x :b: []) erec)) => ?;
      last by iApply wp_stuck_rec_open.
    iApply wp_value; first exact: to_val_rec.
    rewrite/erec. set γ' := (delete _ _).
    iLöb as "Hvrec". rewrite {2}low_val. iAlways. iNext.
    iIntros (v2) "#Hv2". case: (decide (x = f))=>?.
    { subst. rewrite -> subst_subst'; last done.	(* ssr rewrite fails *)
      rewrite of_val_rec subst_substitute; last by rewrite lookup_delete.
      iApply ("IHe" with "[$Hh] [] [$He]").
      rewrite insert_delete. iApply (low_env_insert with "[$Hvrec] []");
        first by rewrite lookup_delete.
      by iApply (low_env_delete with "[$Hγ]"). }
    rewrite of_val_rec subst_substitute; last by rewrite lookup_delete.
    rewrite subst_substitute; last by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply ("IHe" with "[$Hh] [] [$He]").
    iApply (low_env_insert with "[$Hv2] []"); first by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply (low_env_insert with "[$Hvrec] []"); first by rewrite
      lookup_delete.
    do 2!iApply low_env_delete. iExact "Hγ".
  Qed.
  Hint Extern 1 (_ ⊢ confined (Rec _ _ _))
    => rewrite -confined_rec; exact: always_intro.

  Lemma confined_app e1 e2 : confined e1 ∗ confined e2 -∗ confined (App e1 e2).
  Proof.
    rewrite (confined_alt (App _ _)).
    iIntros "[IHe1 IHe2]". iIntros (γ Φ) "#Hh #Hγ Happ HΦ".
    rewrite low_expr substitute_expr. iDestruct "Happ" as "(He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_app with "[$Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (App _ _)) => rewrite -confined_app.

  Lemma confined_lit lit : confined (Lit lit).
  Proof.
    iIntros (γ) "_ _ #?". rewrite low_expr substitute_expr.
    iApply wp_value; first done. by rewrite low_val.
  Qed.
  Hint Extern 1 (_ ⊢ confined (Lit _)) => rewrite -confined_lit.

  Lemma confined_un_op op e : confined e -∗ confined (UnOp op e).
  Proof.
    rewrite (confined_alt (UnOp _ _)).
    iIntros "IHe". iIntros (γ Φ) "Hh Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_un_op with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (UnOp _ _)) => rewrite -confined_un_op.

  Lemma confined_bin_op op e1 e2 :
    confined e1 ∗ confined e2 -∗ confined (BinOp op e1 e2).
  Proof.
    rewrite (confined_alt (BinOp _ _ _)).
    iIntros "[IHe1 IHe2]". iIntros (γ Φ) "#Hh #Hγ Hop HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hop" as "(He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_bin_op with "[$Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (BinOp _ _ _)) => rewrite -confined_bin_op.

  Lemma confined_if e e1 e2 :
    confined e ∗ confined e1 ∗ confined e2 -∗ confined (If e e1 e2).
  Proof.
    rewrite (confined_alt (If _ _ _)).
    iIntros "(IHe&IHe1&IHe2)". iIntros (γ Φ) "#Hh #Hγ Hif HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hif" as "(He&He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "_".
    iApply wp_low_val_if. iNext. iSplit.
    - rewrite confined_alt.
      by iApply ("IHe1" with "[$Hh] [$Hγ] [$He1] [$HΦ]").
    - rewrite (confined_alt e2).
      by iApply ("IHe2" with "[$Hh] [$Hγ] [$He2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (If _ _ _)) => rewrite -confined_if.

  Lemma confined_pair e1 e2 :
    confined e1 ∗ confined e2 -∗ confined (Pair e1 e2).
  Proof.
    rewrite (confined_alt (Pair _ _)).
    iIntros "[IHe1 IHe2]". iIntros (γ Φ) "#Hh #Hγ Hp HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hp" as "(He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    iApply wp_value; first by rewrite /= (to_of_val v1) (to_of_val v2).
    iApply "HΦ". rewrite (low_val (PairV _ _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ confined (Pair _ _)) => rewrite -confined_pair.

  Lemma confined_fst e : confined e -∗ confined (Fst e).
  Proof.
    rewrite (confined_alt (Fst _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_fst with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Fst _)) => rewrite -confined_fst.

  Lemma confined_snd e : confined e -∗ confined (Snd e).
  Proof.
    rewrite (confined_alt (Snd _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_snd with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Snd _)) => rewrite -confined_snd.

  Lemma confined_inl e : confined e -∗ confined (InjL e).
  Proof.
    rewrite (confined_alt (InjL _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply wp_value; first by rewrite /= (to_of_val v).
    iApply "HΦ". rewrite (low_val (InjLV _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ confined (InjL _)) => rewrite -confined_inl.

  Lemma confined_inr e : confined e -∗ confined (InjR e).
  Proof.
    rewrite (confined_alt (InjR _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply wp_value; first by rewrite /= (to_of_val v).
    iApply "HΦ". rewrite (low_val (InjRV _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ confined (InjR _)) => rewrite -confined_inr.

  Lemma confined_case e e1 e2 :
    confined e ∗ confined e1 ∗ confined e2 -∗ confined (Case e e1 e2).
  Proof.
    rewrite (confined_alt (Case _ _ _)).
    iIntros "(IHe&IHe1&IHe2)". iIntros (γ Φ) "#Hh #Hγ Hc HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hc" as "(He&He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply (wp_low_val_case with "[$Hv]"). iNext. iIntros (v0) "#Hv0". iSplit.
    - wp_bind (γ _). rewrite confined_alt.
      iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
      by iApply (wp_low_val_app with "[$Hv1 $Hv0] [$HΦ]").
    - wp_bind (γ _). rewrite (confined_alt e2).
      iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
      by iApply (wp_low_val_app with "[$Hv2 $Hv0] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Case _ _ _)) => rewrite -confined_case.

  Lemma confined_assert e : confined (Assert e).
  Proof. iIntros (γ) "_ _ He". rewrite low_expr. by iExFalso. Qed.
  Hint Extern 1 (_ ⊢ confined (Assert _)) => rewrite -confined_assert.

  Lemma confined_fork e : confined e -∗ confined (Fork e).
  Proof.
    iIntros "IHe". iIntros (γ) "#Hh #Hγ He".
    rewrite low_expr substitute_expr. iApply wp_fork. iNext. iSplit.
    - by rewrite low_val low_lit.
    - rewrite confined_alt.
      iApply ("IHe" with "[$Hh] [$Hγ] [$He] []"). by iIntros.
  Qed.
  Hint Extern 1 (_ ⊢ confined (Fork _)) => rewrite -confined_fork.

  Lemma confined_alloc e : confined e -∗ confined (Alloc e).
  Proof.
    rewrite (confined_alt (Alloc _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply (wp_alloc_low with "[$Hh $Hv]"); [by rewrite to_of_val|done|].
    iNext. iIntros (l) "#Hl". iApply "HΦ". by rewrite low_val low_lit.
  Qed.
  Hint Extern 1 (_ ⊢ confined (Alloc _)) => rewrite -confined_alloc.

  Lemma confined_load e : confined e -∗ confined (Load e).
  Proof.
    rewrite (confined_alt (Load _)).
    iIntros "IHe". iIntros (γ Φ) "#Hh #Hγ He HΦ".
    rewrite low_expr substitute_expr.
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe" with "[$Hh] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_load with "[$Hh $Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Load _)) => rewrite -confined_load.

  Lemma confined_store e1 e2 :
    confined e1 ∗ confined e2 -∗ confined (Store e1 e2).
  Proof.
    rewrite (confined_alt (Store _ _)).
    iIntros "[IHe1 IHe2]". iIntros (γ Φ) "#Hh #Hγ Hstore HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hstore" as "(He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_store with "[$Hh $Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (Store _ _)) => rewrite -confined_store.

  Lemma confined_cas e0 e1 e2 :
    confined e0 ∗ confined e1 ∗ confined e2 -∗ confined (CAS e0 e1 e2).
  Proof.
    rewrite (confined_alt (CAS _ _ _)).
    iIntros "(IHe0&IHe1&IHe2)". iIntros (γ Φ) "#Hh #Hγ Hcas HΦ".
    rewrite low_expr substitute_expr. iDestruct "Hcas" as "(He0&He1&He2)".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe0" with "[$Hh] [$Hγ] [$He0]"). iIntros (v0) "Hv0".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe1" with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "_".
    wp_bind (γ _). rewrite confined_alt.
    iApply ("IHe2" with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_cas with "[$Hh $Hv0 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ confined (CAS _ _ _)) => rewrite -confined_cas.

  Hint Extern 2 =>
    match goal with
    | IH : True ⊢ confined ?e |- True ⊢ confined (_ ?e) => rewrite IH
    end.
  Hint Extern 2 =>
    match goal with
    | IH1 : True ⊢ confined ?e1, IH2 : True ⊢ confined ?e2
      |- True ⊢ confined (_ ?e1 ?e2)
      => rewrite (True_sep_1 True) {1}IH1 IH2
    end.
  Hint Extern 2 =>
    match goal with
    | IH1 : True ⊢ confined ?e1, IH2 : True ⊢ confined ?e2,
      IH3 : True ⊢ confined ?e3 |- True ⊢ confined (_ ?e1 ?e2 ?e3)
      => rewrite (True_sep_1 True) {2}(True_sep_1 True) {1}IH1 {1}IH2 IH3
    end.

  Theorem ftlr' e : confined e.
  Proof. rewrite/uPred_valid. by induction e; auto. Qed.

  Corollary ftlr γ e Φ :
    heap_ctx -∗ low γ -∗ low e -∗ (∀ v, low v -∗ Φ v) -∗ WP γ e ?{{ Φ }}.
  Proof.
    iIntros "Hh Hγ He". rewrite -wp_wand.
    by iApply (ftlr' with "[$Hh] [$Hγ] [$He]").
  Qed.
End ftlr.

(** * Contexts *)
(**
  Contexts are expressions with a single hole. The following
  definition must agree with [heap_lang.expr].
 *)
Inductive ctx :=
  | CHole
  | CRec of binder & binder & ctx
  | CAppL of ctx & expr
  | CAppR of expr & ctx
  | CUnOp of un_op & ctx
  | CBinOpL of bin_op & ctx & expr
  | CBinOpR of bin_op & expr & ctx
  | CIf of ctx & expr & expr
  | CIfL of expr & ctx & expr
  | CIfR of expr & expr & ctx
  | CPairL of ctx & expr
  | CPairR of expr & ctx
  | CFst of ctx
  | CSnd of ctx
  | CInjL of ctx
  | CInjR of ctx
  | CCase of ctx & expr & expr
  | CCaseL of expr & ctx & expr
  | CCaseR of expr & expr & ctx
  | CAssert of ctx
  | CFork of ctx
  | CAlloc of ctx
  | CLoad of ctx
  | CStoreL of ctx & expr
  | CStoreR of expr & ctx
  | CCASL of ctx & expr & expr
  | CCASM of expr & ctx & expr
  | CCASR of expr & expr & ctx.

Fixpoint ctx_fill (C : ctx) (e : expr) : expr :=
  let rec := λ C, ctx_fill C e in
  match C with
  | CHole => e
  | CRec f x C => Rec f x (rec C)
  | CAppL C1 e2 => App (rec C1) e2
  | CAppR e1 C2 => App e1 (rec C2)
  | CUnOp op C => UnOp op (rec C)
  | CBinOpL op C1 e2 => BinOp op (rec C1) e2
  | CBinOpR op e1 C2 => BinOp op e1 (rec C2)
  | CIf C0 e1 e2 => If (rec C0) e1 e2
  | CIfL e0 C1 e2 => If e0 (rec C1) e2
  | CIfR e0 e1 C2 => If e0 e1 (rec C2)
  | CPairL C1 e2 => Pair (rec C1) e2
  | CPairR e1 C2 => Pair e1 (rec C2)
  | CFst C => Fst (rec C)
  | CSnd C => Snd (rec C)
  | CInjL C => InjL (rec C)
  | CInjR C => InjR (rec C)
  | CCase C0 e1 e2 => Case (rec C0) e1 e2
  | CCaseL e0 C1 e2 => Case e0 (rec C1) e2
  | CCaseR e0 e1 C2 => Case e0 e1 (rec C2)
  | CAssert C => Assert (rec C)
  | CFork C => Fork (rec C)
  | CAlloc C => Alloc (rec C)
  | CLoad C => Load (rec C)
  | CStoreL C1 e2 => Store (rec C1) e2
  | CStoreR e1 C2 => Store e1 (rec C2)
  | CCASL C0 e1 e2 => CAS (rec C0) e1 e2
  | CCASM e0 C1 e2 => CAS e0 (rec C1) e2
  | CCASR e0 e1 C2 => CAS e0 e1 (rec C2)
  end.

(**
	A (syntactically) low context contains neither assertions nor
	high locations. (We reserve assertions for verified code.)
*)
Section low_ctx.
  Context `{heapG Σ}.
  Implicit Types C : ctx.

  Definition lowctx : ctx → iProp Σ :=
    fix rec C := match C with
    | CHole => True
    | CAssert _ => False
    | CRec _ _ C | CUnOp _ C | CFst C | CSnd C | CInjL C | CInjR C
    | CFork C | CAlloc C | CLoad C
      => rec C
    | CAppL C1 e2 | CBinOpL _ C1 e2 | CPairL C1 e2 | CStoreL C1 e2
      => rec C1 ∗ low e2
    | CAppR e1 C2 | CBinOpR _ e1 C2 | CPairR e1 C2 | CStoreR e1 C2
      => low e1 ∗ rec C2
    | CIf C0 e1 e2 | CCase C0 e1 e2 | CCASL C0 e1 e2
      => rec C0 ∗ low e1 ∗ low e2
    | CIfL e0 C1 e2 | CCaseL e0 C1 e2 | CCASM e0 C1 e2
      => low e0 ∗ rec C1 ∗ low e2
    | CIfR e0 e1 C2 | CCaseR e0 e1 C2 | CCASR e0 e1 C2
      => low e0 ∗ low e1 ∗ rec C2
    end%I.
  Global Instance lowctx_persistent C : PersistentP (lowctx C).
  Proof. rewrite/lowctx; elim: C=>//; rewrite-/lowctx; by apply _. Qed.
  Global Instance lowctx_low : LowIntegrity Σ ctx := Low lowctx _.
  Global Instance lowctx_timeless (C : ctx) : TimelessP (low C).
  Proof. rewrite/lowctx; elim: C=>//; rewrite-/lowctx; by apply _. Qed.

  Lemma low_ctx C :
    low C ⊣⊢
    match C with
    | CHole => True
    | CAssert _ => False
    | CRec _ _ C | CUnOp _ C | CFst C | CSnd C | CInjL C | CInjR C
    | CFork C | CAlloc C | CLoad C
      => low C
    | CAppL C1 e2 | CBinOpL _ C1 e2 | CPairL C1 e2 | CStoreL C1 e2
      => low C1 ∗ low e2
    | CAppR e1 C2 | CBinOpR _ e1 C2 | CPairR e1 C2 | CStoreR e1 C2
      => low e1 ∗ low C2
    | CIf C0 e1 e2 | CCase C0 e1 e2 | CCASL C0 e1 e2
      => low C0 ∗ low e1 ∗ low e2
    | CIfL e0 C1 e2 | CCaseL e0 C1 e2 | CCASM e0 C1 e2
      => low e0 ∗ low C1 ∗ low e2
    | CIfR e0 e1 C2 | CCaseR e0 e1 C2 | CCASR e0 e1 C2
      => low e0 ∗ low e1 ∗ low C2
    end%I.
  Proof. by case: C. Qed.
End low_ctx.

(** Sanity check. *)
(**
	To catch changes to [expr] that aren't reflected in [ctx], we
	embed evaluation contexts in contexts and prove the filling
	functions match up.
*)
Local Notation ectx := (list ectx_item).

Definition of_ectx_item (Ki : ectx_item) (C : ctx) : ctx :=
  match Ki with
  | AppLCtx e2 => CAppL C e2
  | AppRCtx v1 => CAppR (of_val v1) C
  | UnOpCtx op => CUnOp op C
  | BinOpLCtx op e2 => CBinOpL op C e2
  | BinOpRCtx op v1 => CBinOpR op (of_val v1) C
  | IfCtx e1 e2 => CIf C e1 e2
  | PairLCtx e2 => CPairL C e2
  | PairRCtx v1 => CPairR (of_val v1) C
  | FstCtx => CFst C
  | SndCtx => CSnd C
  | InjLCtx => CInjL C
  | InjRCtx => CInjR C
  | CaseCtx e1 e2 => CCase C e1 e2
  | AssertCtx => CAssert C
  | AllocCtx => CAlloc C
  | LoadCtx => CLoad C
  | StoreLCtx e2 => CStoreL C e2
  | StoreRCtx v1 => CStoreR (of_val v1) C
  | CasLCtx e1 e2 => CCASL C e1 e2
  | CasMCtx v0 e2 => CCASM (of_val v0) C e2
  | CasRCtx v0 v1 => CCASR (of_val v0) (of_val v1) C
  end.

Definition of_ectx : ectx → ctx := foldr of_ectx_item CHole.

Fixpoint to_ectx (C : ctx) : option ectx :=
  let rec := λ C Ki, K ← to_ectx C; Some (Ki :: K) in
  let recv := λ e C f, v ← to_val e; rec C $ f v in
  match C with
  | CHole => Some []
  | CAppL C e2 => rec C $ AppLCtx e2
  | CAppR e1 C => recv e1 C $ AppRCtx
  | CUnOp op C => rec C $ UnOpCtx op
  | CBinOpL op C e2 => rec C $ BinOpLCtx op e2
  | CBinOpR op e1 C => recv e1 C $ BinOpRCtx op
  | CIf C e1 e2 => rec C $ IfCtx e1 e2
  | CPairL C e2 => rec C $ PairLCtx e2
  | CPairR e1 C => recv e1 C PairRCtx
  | CFst C => rec C FstCtx
  | CSnd C => rec C SndCtx
  | CInjL C => rec C InjLCtx
  | CInjR C => rec C InjRCtx
  | CCase C e1 e2 => rec C $ CaseCtx e1 e2
  | CAssert C => rec C AssertCtx
  | CAlloc C => rec C AllocCtx
  | CLoad C => rec C LoadCtx
  | CStoreL C e2 => rec C $ StoreLCtx e2
  | CStoreR e1 C => recv e1 C StoreRCtx
  | CCASL C e1 e2 => rec C $ CasLCtx e1 e2
  | CCASM e0 C e2 => v0 ← to_val e0; rec C $ CasMCtx v0 e2
  | CCASR e0 e1 C => v0 ← to_val e0; v1 ← to_val e1; rec C $ CasRCtx v0 v1
  | _ => None
  end.

Lemma to_of_ectx K : to_ectx (of_ectx K) = Some K.
Proof.
  elim: K => // Ki K IH. by destruct Ki; simplify_option_eq; repeat f_equal.
Qed.

Lemma of_to_ectx C K : to_ectx C = Some K → of_ectx K = C.
Proof.
  elim: C K; intros; simplify_option_eq; auto using of_to_val with f_equal.
Qed.

Instance of_ectx_inj : Inj (=) (=) of_ectx.
Proof. move=>?? EQ. apply (inj Some). by rewrite -!to_of_ectx EQ. Qed.

Lemma to_ectx_fill C K e : to_ectx C = Some K → ctx_fill C e = fill K e.
Proof.
  elim: C K; intros; simplify_option_eq;
    auto using of_to_val, eq_sym with f_equal.
Qed.

(** * Adversaries *)
(**
	To state the [robust_safety] theorem, we define a special case
	of [low_ctx] at the meta-level. An _adversarial context_ is a
	heap language context containing neither locations nor
	assertions.
*)
Definition adv_lit : base_lit → Prop :=
  λ lit, match lit with
  | LitInt _ | LitBool _ | LitUnit => True
  | LitLoc _ => False
  end.

Definition adv_expr : expr → Prop :=
  fix rec e := match e with
  | Var _ => True
  | Assert _ => False
  | Lit lit => adv_lit lit
  | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e | InjR e
  | Fork e | Alloc e | Load e
    => rec e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 => rec e1 ∧ rec e2
  | If e1 e2 e3 | Case e1 e2 e3 | CAS e1 e2 e3
    => rec e1 ∧ rec e2 ∧ rec e3
  end.

Definition adv_ctx : ctx → Prop :=
  fix rec C := match C with
  | CHole => True
  | CAssert _ => False
  | CRec _ _ C | CUnOp _ C | CFst C | CSnd C | CInjL C | CInjR C
  | CFork C | CAlloc C | CLoad C
    => rec C
  | CAppL C1 e2 | CBinOpL _ C1 e2 | CPairL C1 e2 | CStoreL C1 e2
    => rec C1 ∧ adv_expr e2
  | CAppR e1 C2 | CBinOpR _ e1 C2 | CPairR e1 C2 | CStoreR e1 C2
    => adv_expr e1 ∧ rec C2
  | CIf C0 e1 e2 | CCase C0 e1 e2 | CCASL C0 e1 e2
    => rec C0 ∧ adv_expr e1 ∧ adv_expr e2
  | CIfL e0 C1 e2 | CCaseL e0 C1 e2 | CCASM e0 C1 e2
    => adv_expr e0 ∧ rec C1 ∧ adv_expr e2
  | CIfR e0 e1 C2 | CCaseR e0 e1 C2 | CCASR e0 e1 C2
    => adv_expr e0 ∧ adv_expr e1 ∧ rec C2
  end.

Section adversary.
    Context `{heapG Σ}.
  Implicit Types C : ctx.
  Implicit Types e : expr.

  Lemma adv_lit_low lit : adv_lit lit → low lit.
  Proof. by case: lit. Qed.

  Lemma adv_expr_low e : adv_expr e → low e.
  Proof.	(* PDS: Automate. *)
    elim: e => //.
    - move=>e1 IH1 e2 IH2 [] ??. rewrite low_expr /=.
      iIntros. iSplit. by iApply IH1. by iApply IH2.
    - exact: adv_lit_low.
    - move=>op e1 IH1 e2 IH2 [] ??. rewrite low_expr /=.
      iIntros. iSplit. by iApply IH1. by iApply IH2.
    - move=>e0 IH0 e1 IH1 e2 IH2 [] ? [] ?. rewrite low_expr /=.
      iIntros. iSplit; last iSplit. by iApply IH0. by iApply IH1. by iApply IH2.
    - move=>e1 IH1 e2 IH2 [] ??. rewrite low_expr /=.
      iIntros. iSplit. by iApply IH1. by iApply IH2.
    - move=>e0 IH0 e1 IH1 e2 IH2 [] ? [] ?. rewrite low_expr /=.
      iIntros. iSplit; last iSplit. by iApply IH0. by iApply IH1. by iApply IH2.
    - move=>e1 IH1 e2 IH2 [] ??. rewrite low_expr /=.
      iIntros. iSplit. by iApply IH1. by iApply IH2.
    - move=>e0 IH0 e1 IH1 e2 IH2 [] ? [] ?. rewrite low_expr /=.
      iIntros. iSplit; last iSplit. by iApply IH0. by iApply IH1. by iApply IH2.
  Qed.

  Lemma adv_ctx_low C : adv_ctx C → low C.
  Proof.	(* PDS: Automate. *)
    elim: C => //=.
    (* application *)
    - move=>C1 IH e2 [] ??. rewrite low_ctx.
      iSplit. by iApply IH. by iApply adv_expr_low.
    - move=>e1 C2 IH [] ??. rewrite low_ctx.
      iSplit. by iApply adv_expr_low. by iApply IH.
    (* binary operations *)
    - move=>op C1 IH e2 [] ??. rewrite low_ctx.
      iSplit. by iApply IH. by iApply adv_expr_low.
    - move=>op e1 C2 IH [] ??. rewrite low_ctx.
      iSplit. by iApply adv_expr_low. by iApply IH.
    (* if *)
    - move=>C0 IH e1 e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply IH. by iApply adv_expr_low.
      by iApply adv_expr_low.
    - move=>e0 C1 IH e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply IH.
      by iApply adv_expr_low.
    - move=>e0 e1 C2 IH [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply adv_expr_low.
      by iApply IH.
    (* pairing *)
    - move=>C1 IH e2 [] ??. rewrite low_ctx.
      iSplit. by iApply IH. by iApply adv_expr_low.
    - move=>e1 C2 IH [] ??. rewrite low_ctx.
      iSplit. by iApply adv_expr_low. by iApply IH.
    (* case *)
    - move=>C0 IH e1 e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply IH. by iApply adv_expr_low.
      by iApply adv_expr_low.
    - move=>e0 C1 IH e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply IH.
      by iApply adv_expr_low.
    - move=>e0 e1 C2 IH [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply adv_expr_low.
      by iApply IH.
    (* store *)
    - move=>C1 IH e2 [] ??. rewrite low_ctx.
      iSplit. by iApply IH. by iApply adv_expr_low.
    - move=>e1 C2 IH [] ??. rewrite low_ctx.
      iSplit. by iApply adv_expr_low. by iApply IH.
    (* CAS *)
    - move=>C0 IH e1 e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply IH. by iApply adv_expr_low.
      by iApply adv_expr_low.
    - move=>e0 C1 IH e2 [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply IH.
      by iApply adv_expr_low.
    - move=>e0 e1 C2 IH [] ? [] ??. rewrite low_ctx.
      iSplit; [|iSplit]. by iApply adv_expr_low. by iApply adv_expr_low.
      by iApply IH.
  Qed.
End adversary.

(** * Robust safety *)
(**
	Our aim is to show that, under the heap invariant, if we plug
	a closed, semantically low expression (i.e., verified code)
	into a syntactically low context (i.e., an adversary), the
	resulting expression is semantically low.

	The proof is by induction on contexts, using the FTLR to zap
	the context's subexpressions to low values. As in the proof of
	the FTLR, we must generalize to account for substitution.
 *)
Section robust_safety.

  Context `{heapG Σ}.
  Implicit Types γ : env.
  Implicit Types C : ctx.
  Implicit Types e : expr.
  Implicit Types v : val.
  Existing Instance env_low.

  Definition verified : pbit → expr → iProp Σ := λ p e, (
     ⌜Closed [] e⌝ ∗ WP e @ p; ⊤ {{ low }}
  )%I.

  Definition safe : ctx → iProp Σ := λ C, (
    ∀ γ p e, heap_ctx -∗ low C -∗ low γ -∗ □ verified p e -∗
    WP γ (ctx_fill C e) ?{{ low }}
  )%I.

  Lemma verified_alt p e :
    verified p e ⊣⊢
    ⌜Closed [] e⌝ ∗ ∀ Φ, (∀ v, low v -∗ Φ v) -∗ WP e @ p; ⊤ {{ Φ }}.
  Proof.
    iSplit.
    - iIntros "(%&He)". iSplit; first done. iIntros (Φ). by rewrite -wp_wand.
    - iIntros "(%&He)". iSplit; first done. iApply "He". by iIntros.
  Qed.

  Lemma safe_alt C :
    safe C ⊣⊢
    ∀ γ p e Φ, heap_ctx -∗ low C -∗ low γ -∗ □ verified p e -∗
    (∀ v, low v -∗ Φ v) -∗ WP γ (ctx_fill C e) ?{{ Φ }}.
  Proof.
    iSplit.
    - iIntros "Hsafe". iIntros (γ p e Φ) "Hh HC Hγ He".
      rewrite -wp_wand. by iApply ("Hsafe" with "[$Hh] [$HC] [$Hγ] [$He]").
    - iIntros "Halt". iIntros (γ p e) "Hh HC Hγ He".
      iApply ("Halt" with "[$Hh] [$HC] [$Hγ] [$He] []"). by iIntros.
  Qed.

  Lemma safe_hole : safe CHole.
  Proof.
    iIntros (γ p e) "_ _ _ >(%&He) /=". iApply (wp_forget_progress p).
    by rewrite substitute_closed.
  Qed.
  Hint Extern 1 (_ ⊢ safe CHole) => rewrite -safe_hole.

  Lemma safe_rec f x C : □ safe C -∗ safe (CRec f x C).
  Proof.
    (* PDS: Lots of duplication with confined_rec. *)
    iIntros "#IH". iIntros (γ p e) "#Hh #HC #Hγ #He /=".
    rewrite low_ctx substitute_expr. set erec := substitute _ _.
    case: (decide (Closed (f :b: x :b: []) erec)) => ?;
      last by iApply wp_stuck_rec_open.
    iApply wp_value; first exact: to_val_rec.
    rewrite/erec. set γ' := (delete _ _).
    iLöb as "Hvrec". rewrite {2}low_val. iAlways. iNext.
    iIntros (v2) "#Hv2". case: (decide (x = f))=>?.
    { subst. rewrite -> subst_subst'; last done.	(* ssr rewrite fails *)
      rewrite of_val_rec subst_substitute; last by rewrite lookup_delete.
      iApply ("IH" with "[$Hh] [$HC] [] [He]"); last iExact "He". (* iNext bug *)
      rewrite insert_delete. iApply (low_env_insert with "[$Hvrec] []");
        first by rewrite lookup_delete.
      by iApply (low_env_delete with "[$Hγ]"). }
    rewrite of_val_rec subst_substitute; last by rewrite lookup_delete.
    rewrite subst_substitute; last by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply ("IH" with "[$Hh] [$HC] [] [He]"); last iExact "He". (* iNext bug *)
    iApply (low_env_insert with "[$Hv2] []"); first by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply (low_env_insert with "[$Hvrec] []"); first by rewrite
      lookup_delete.
    do 2!iApply low_env_delete. iExact "Hγ".
  Qed.
  Hint Extern 1 (_ ⊢ safe (CRec _ _ _))
    => rewrite -safe_rec; exact: always_intro.

  Lemma safe_app_l C1 e2 : safe C1 -∗ safe (CAppL C1 e2).
  Proof.
    rewrite (safe_alt (CAppL _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Happ #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Happ" as "(HC1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (v1) "Hv1".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_app with "[$Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CAppL _ _)) => rewrite -safe_app_l.

  Lemma safe_app_r e1 C2 : safe C2 -∗ safe (CAppR e1 C2).
  Proof.
    rewrite (safe_alt (CAppR _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Happ #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Happ" as "(He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_app with "[$Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CAppR _ _)) => rewrite -safe_app_r.

  Lemma safe_un_op op C : safe C -∗ safe (CUnOp op C).
  Proof.
    rewrite (safe_alt (CUnOp _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_un_op with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CUnOp _ _)) => rewrite -safe_un_op.

  Lemma safe_bin_op_l op C1 e2 : safe C1 -∗ safe (CBinOpL op C1 e2).
  Proof.
    rewrite (safe_alt (CBinOpL _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hop #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hop" as "(HC1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (?) "Hv1".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (?) "Hv2".
    by iApply (wp_low_val_bin_op with "[$Hv1 Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CBinOpL _ _ _)) => rewrite -safe_bin_op_l.

  Lemma safe_bin_op_r op e1 C2 : safe C2 -∗ safe (CBinOpR op e1 C2).
  Proof.
    rewrite (safe_alt (CBinOpR _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hop #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hop" as "(He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (?) "Hv1".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (?) "Hv2".
    by iApply (wp_low_val_bin_op with "[$Hv1 Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CBinOpR _ _ _)) => rewrite -safe_bin_op_r.

  Lemma safe_if C e1 e2 : safe C -∗ safe (CIf C e1 e2).
  Proof.
    rewrite (safe_alt (CIf _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hif #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hif" as "(HC&He1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (?) "_".
    iApply wp_low_val_if. iNext. iSplit.
    - by iApply (ftlr with "[$Hh] [$Hγ] [$He1] [$HΦ]").
    - by iApply (ftlr with "[$Hh] [$Hγ] [$He2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CIf _ _ _)) => rewrite -safe_if.

  Lemma safe_if_l e0 C1 e2 : safe C1 -∗ safe (CIfL e0 C1 e2).
  Proof.
    rewrite (safe_alt (CIfL _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hif #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hif" as "(He0&HC1&He2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (?) "_".
    iApply wp_low_val_if. iNext. iSplit.
    - rewrite safe_alt. by iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]").
    - by iApply (ftlr with "[$Hh] [$Hγ] [$He2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CIfL _ _ _)) => rewrite -safe_if_l.

  Lemma safe_if_r e0 e1 C2 : safe C2 -∗ safe (CIfR e0 e1 C2).
  Proof.
    rewrite (safe_alt (CIfR _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hif #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hif" as "(He0&He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (?) "_".
    iApply wp_low_val_if. iNext. iSplit.
    - by iApply (ftlr with "[$Hh] [$Hγ] [$He1] [$HΦ]").
    - rewrite safe_alt. by iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CIfR _ _ _)) => rewrite -safe_if_r.

  Lemma safe_pair_l C1 e2 : safe C1 -∗ safe (CPairL C1 e2).
  Proof.
    rewrite (safe_alt (CPairL _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hp #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hp" as "(HC1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (v1) "Hv1".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    iApply wp_value; first by rewrite /= (to_of_val v1) (to_of_val v2).
    iApply "HΦ". rewrite (low_val (PairV _ _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CPairL _ _)) => rewrite -safe_pair_l.

  Lemma safe_pair_r e1 C2 : safe C2 -∗ safe (CPairR e1 C2).
  Proof.
    rewrite (safe_alt (CPairR _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hp #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hp" as "(He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (v2) "Hv2".
    iApply wp_value; first by rewrite /= (to_of_val v1) (to_of_val v2).
    iApply "HΦ". rewrite (low_val (PairV _ _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CPairR _ _)) => rewrite -safe_pair_r.

  Lemma safe_fst C : safe C -∗ safe (CFst C).
  Proof.
    rewrite (safe_alt (CFst _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_fst with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CFst _)) => rewrite -safe_fst.

  Lemma safe_snd C : safe C -∗ safe (CSnd C).
  Proof.
    rewrite (safe_alt (CSnd _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_snd with "[$Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CSnd _)) => rewrite -safe_snd.

  Lemma safe_inl C : safe C -∗ safe (CInjL C).
  Proof.
    rewrite (safe_alt (CInjL _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply wp_value; first by rewrite /= (to_of_val v).
    iApply "HΦ". rewrite (low_val (InjLV _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CInjL _)) => rewrite -safe_inl.

  Lemma safe_inr C : safe C -∗ safe (CInjR C).
  Proof.
    rewrite (safe_alt (CInjR _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply wp_value; first by rewrite /= (to_of_val v).
    iApply "HΦ". rewrite (low_val (InjRV _)). by iFrame.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CInjR _)) => rewrite -safe_inr.

  Lemma safe_case C e1 e2 : safe C -∗ safe (CCase C e1 e2).
  Proof.
    rewrite (safe_alt (CCase _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(HC&He1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply (wp_low_val_case with "[$Hv]"). iNext. iIntros (v0) "#Hv0".
    iSplit; wp_bind (γ _).
    - iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
      by iApply (wp_low_val_app with "[$Hv1 $Hv0] [$HΦ]").
    - iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
      by iApply (wp_low_val_app with "[$Hv2 $Hv0] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCase _ _ _)) => rewrite -safe_case.

  Lemma safe_case_l e0 C1 e2 : safe C1 -∗ safe (CCaseL e0 C1 e2).
  Proof.
    rewrite (safe_alt (CCaseL _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(He0&HC1&He2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (v) "Hv".
    iApply (wp_low_val_case with "[$Hv]"). iNext. iIntros (v0) "#Hv0".
    iSplit; wp_bind (γ _).
    - rewrite safe_alt.
      iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (v1) "Hv1".
      by iApply (wp_low_val_app with "[$Hv1 $Hv0] [$HΦ]").
    - iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
      by iApply (wp_low_val_app with "[$Hv2 $Hv0] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCaseL _ _ _)) => rewrite -safe_case_l.

  Lemma safe_case_r e0 e1 C2 : safe C2 -∗ safe (CCaseR e0 e1 C2).
  Proof.
    rewrite (safe_alt (CCaseR _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(He0&He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (v) "Hv".
    iApply (wp_low_val_case with "[$Hv]"). iNext. iIntros (v0) "#Hv0".
    iSplit; wp_bind (γ _).
    - iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
      by iApply (wp_low_val_app with "[$Hv1 $Hv0] [$HΦ]").
    - rewrite safe_alt.
      iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (v2) "Hv2".
      by iApply (wp_low_val_app with "[$Hv2 $Hv0] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCaseR _ _ _)) => rewrite -safe_case_r.

  Lemma safe_assert C : safe (CAssert C).
  Proof. iIntros (γ p e) "_ Hc _ _ /=". rewrite low_ctx. by iExFalso. Qed.
  Hint Extern 1 (_ ⊢ safe (CAssert _)) => rewrite -safe_assert.

  Lemma safe_fork C : safe C -∗ safe (CFork C).
  Proof.
    rewrite (safe_alt (CFork _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iApply wp_fork. iNext. iSplitL "HΦ".
    - iApply "HΦ". by rewrite low_val low_lit.
    - rewrite safe_alt. iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]").
      by iIntros.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CFork _)) => rewrite -safe_fork.

  Lemma safe_alloc C : safe C -∗ safe (CAlloc C).
  Proof.
    rewrite (safe_alt (CAlloc _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    iApply (wp_alloc_low with "[$Hh $Hv]"); [by rewrite to_of_val|done|].
    iNext. iIntros (l) "#Hl". iApply "HΦ". by rewrite low_val low_lit.
  Qed.
  Hint Extern 1 (_ ⊢ safe (CAlloc _)) => rewrite -safe_alloc.

  Lemma safe_load C : safe C -∗ safe (CLoad C).
  Proof.
    rewrite (safe_alt (CLoad _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh HC #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr.
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v) "Hv".
    by iApply (wp_low_val_load with "[$Hh $Hv] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CLoad _)) => rewrite -safe_load.

  Lemma safe_store_l C1 e2 : safe C1 -∗ safe (CStoreL C1 e2).
  Proof.
    rewrite (safe_alt (CStoreL _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hp #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hp" as "(HC1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (v1) "Hv1".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_store with "[$Hh $Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CStoreL _ _)) => rewrite -safe_store_l.

  Lemma safe_store_r e1 C2 : safe C2 -∗ safe (CStoreR e1 C2).
  Proof.
    rewrite (safe_alt (CStoreR _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hp #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hp" as "(He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "Hv1".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_store with "[$Hh $Hv1 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CStoreR _ _)) => rewrite -safe_store_r.

  Lemma safe_cas_l C e1 e2 : safe C -∗ safe (CCASL C e1 e2).
  Proof.
    rewrite (safe_alt (CCASL _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(HC&He1&He2)".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC] [$Hγ] [$He]"). iIntros (v0) "Hv0".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "_".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_cas with "[$Hh $Hv0 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCASL _ _ _)) => rewrite -safe_cas_l.

  Lemma safe_cas_m e0 C1 e2 : safe C1 -∗ safe (CCASM e0 C1 e2).
  Proof.
    rewrite (safe_alt (CCASM _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(He0&HC1&He2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (v0) "Hv0".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC1] [$Hγ] [$He]"). iIntros (v1) "Hv1".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He2]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_cas with "[$Hh $Hv0 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCASM _ _ _)) => rewrite -safe_cas_m.

  Lemma safe_cas_r e0 e1 C2 : safe C2 -∗ safe (CCASR e0 e1 C2).
  Proof.
    rewrite (safe_alt (CCASR _ _ _)).
    iIntros "IH". iIntros (γ p e Φ) "#Hh Hc #Hγ He HΦ /=".
    rewrite low_ctx substitute_expr. iDestruct "Hc" as "(He0&He1&HC2)".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He0]"). iIntros (v0) "Hv0".
    wp_bind (γ _).
    iApply (ftlr with "[$Hh] [$Hγ] [$He1]"). iIntros (v1) "_".
    wp_bind (γ _). rewrite safe_alt.
    iApply ("IH" with "[$Hh] [$HC2] [$Hγ] [$He]"). iIntros (v2) "Hv2".
    by iApply (wp_low_val_cas with "[$Hh $Hv0 $Hv2] [$HΦ]").
  Qed.
  Hint Extern 1 (_ ⊢ safe (CCASR _ _ _)) => rewrite -safe_cas_r.

  Hint Extern 2 =>
    match goal with
    | IH : True ⊢ safe ?C |- True ⊢ safe (_ ?C) => rewrite IH
    end.

  Theorem robust_safetyI' C : safe C.
  Proof. rewrite/uPred_valid. by induction C; auto. Qed.

  (** The internal version of [robust_safety]. *)
  Corollary robust_safetyI C γ p e Φ `{!Closed [] e} :
    heap_ctx -∗ low C -∗ low γ -∗ □ WP e @ p; ⊤ {{ low }} -∗
    (∀ v, low v -∗ Φ v) -∗ WP γ (ctx_fill C e) ?{{ Φ }}.
  Proof.
    iIntros "Hh HC Hγ #He". rewrite -wp_wand.
    iApply (robust_safetyI' with "[$Hh] [$HC] [$Hγ]"). by iAlways; iSplit.
  Qed.
End robust_safety.
