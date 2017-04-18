From iris.proofmode Require Import tactics.

Module fin_maps.	(* cf. ../prelude/fin_maps.v *)
From iris.prelude Require Import fin_maps.
Section union.
  Context `{FinMap K M}.

  Lemma lookup_union_Some_r' {A} (m1 m2 : M A) i x :
    m1 !! i = None → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x.
  Proof. rewrite lookup_union_Some_raw; intuition. Qed.

  (* TODO: There's likely a much shorter proof. *)
  Lemma delete_insert_union {A} (m1 m2 : M A) i x :
    m1 !! i = Some x → m2 !! i = None → m1 ∪ m2 = delete i m1 ∪ <[i:=x]> m2.
  Proof.
    transitivity (m1 ∪ {[i:=x]} ∪ m2).
    { f_equal. apply map_eq => i'.
      case: (decide (i = i'))=> [<-|?]; first by simplify_map_eq.
      case EQ: (m1 !! i')=> [hv|]; first by simplify_map_eq.
      symmetry. apply lookup_union_None. by simplify_map_eq. }
    rewrite (insert_union_singleton_l m2 i x) assoc. f_equal.
    apply map_eq => i'. case: (decide (i = i'))=> [<-|?]; simplify_map_eq.
    { symmetry. rewrite lookup_union_Some_raw. right. by simplify_map_eq. }
    case EQ: (m1 !! i')=>[hv|]; simplify_map_eq.
    { symmetry. rewrite lookup_union_Some_raw. left. by simplify_map_eq. }
    by transitivity (None : option A); [| symmetry];
      apply lookup_union_None; simplify_map_eq.
  Qed.
End union.

Section difference.
  Context `{FinMap K M}.

  Lemma map_difference_empty {A} (m : M A) : m ∖ ∅ = m.
  Proof.
    apply/map_eq=>i. case EQ: (_ !! _)=>[x|].
    - by move: EQ =>/lookup_difference_Some [] ->.
    - move: EQ=>/lookup_difference_None [->//|].
      by rewrite lookup_empty=>/is_Some_None.
  Qed.
End difference.
End fin_maps.

Module list.	(* cf. ../prelude/list.v *)
Section list.
  Context `{EqDecision A}.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma filter_cons l x :
    filter P (x :: l) = if decide (P x) then x :: filter P l else filter P l.
  Proof. by []. Qed.

  Lemma foldr_cons {B} (f : A → B → B) (b : B) (a : A) (l : list A) :
    foldr f b (a :: l) = f a (foldr f b l).
  Proof. by []. Qed.

  Lemma foldr_filter {B} (R : relation B) `{!Equivalence R}
      (f : A → B → B) (b : B) (l : list A) `{!Proper ((=) ==> R ==> R) f}
      (Hf : ∀ a b, ¬ P a → R b (f a b)) :
    R (foldr f b (filter P l)) (foldr f b l).
  Proof.
    elim: l=> // a l IH. rewrite filter_cons. case: (decide _)=> /= ?.
    - f_equiv. exact: IH.
    - etrans. exact: IH. exact: Hf.
  Qed.
End list.
End list.

Module algebra_auth.	(* cf. ../algebra/auth.v *)
From iris.algebra Require Import auth.

Section auth.
  Context {A : ucmraT}.
  Implicit Types a b : A.
  Implicit Types x y : auth A.

  Lemma auth_frag_alloc a b `{!CMRADiscrete A, !CMRATotal A}
      (HA : ∀ x : A, Persistent x) :
    b ≼ a → ● a ~~> ● a ⋅ ◯ b.
  Proof.
    move=>[a' ->]. apply auth_update_alloc.
    rewrite -{3}(persistent_core b) -(right_id _ _ (core b)).
    rewrite -{2}(cmra_core_l b) -assoc.
    apply op_local_update_discrete.
    by rewrite assoc cmra_core_l.
  Qed.
End auth.
End algebra_auth.

Module gmap.	(* cf. ../algebra/gmap.v *)
Section gmap.
  From iris.algebra Require Import gmap.

  Context `{Countable K} {A : cmraT}.
  Implicit Types m : gmap K A.

  Lemma insert_op_r i x m1 m2 :
    m1 !! i = None → <[i:=x]>(m1  ⋅ m2) = m1 ⋅ (<[i:=x]>m2).
  Proof.
    intros Hdom. rewrite (insert_merge_r _ _ _ _ _ x).
    done. by rewrite Hdom.
  Qed.
  Lemma insert_op_l i x m1 m2 :
    m2 !! i = None → <[i:=x]>(m1  ⋅ m2) = (<[i:=x]>m1) ⋅ m2.
  Proof.
    intros Hdom. rewrite (insert_merge_l _ _ _ _ _ x).
    done. by rewrite Hdom.
  Qed.
End gmap.
End gmap.

Module csum.	(* cf. ../algebra/csum.v *)
Section csum.
  From iris.algebra Require Import csum.

  Context {A B : cmraT}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma Cinl_included a1 a2 :
    @included (csum A B) _ _ (Cinl a1) (Cinl a2) ↔ a1 ≼ a2.
  Proof.
    rewrite csum_included; split; last by move=>?; right; left; do 2!eexists.
    case => //; case => //; last by move=> [? [? [? _]]]; exfalso.
    by move=> [? [? [[->] [[->] ?]]]].
  Qed.

  Lemma Cinr_included b1 b2 :
    @included (csum A B) _ _ (Cinr b1) (Cinr b2) ↔ b1 ≼ b2.
  Proof.
    rewrite csum_included; split; last by move=>?; right; right; do 2!eexists.
    case => //; case => //; first by move=> [? [? [? _]]]; exfalso.
    by move=> [? [? [[->] [[->] ?]]]].
  Qed.

  Lemma csum_equivE (x y : csum A B) :
    x ≡ y ↔ (match x, y with
              | Cinl a, Cinl a' => a ≡ a'
              | Cinr b, Cinr b' => b ≡ b'
              | CsumBot, CsumBot => True
              | _, _ => False
              end).
  Proof.
    split; first by destruct 1.
    by destruct x, y; try destruct 1; try constructor.
  Qed.
End csum.
End csum.

Module option.	(* cf. ../base_logic/primitive.v:/option_equivI *)
Section option.
  From iris.algebra Require Import ofe.
  Context {A : ofeT}.

  Lemma option_equivE (mx my : option A) :
    mx ≡ my ↔ match mx, my with
               | Some x, Some y => x ≡ y | None, None => True | _, _ => False
               end.
  Proof. split. by destruct 1. by destruct mx, my; try constructor. Qed.
End option.
End option.

Module lib_auth.	(* cf. ../base_logic/lib/auth.v *)
Section auth.
  From iris.base_logic.lib Require Import auth.
  Context `{invG Σ, authG Σ A}.
  Context {T : Type} `{!Inhabited T}.
  Context (f : T → A) (φ : T → iProp Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types a b : A.
  Implicit Types t u : T.
  Implicit Types γ : gname.

  Lemma auth_acc_strong E γ a :
    ▷ auth_inv γ f φ ∗ auth_own γ a ={E}=∗ ∃ t,
      ⌜✓ (f t)⌝ ∗ ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E}=∗ ▷ auth_inv γ f φ ∗ auth_own γ b.
  Proof.
    iIntros "[Hinv Hγf]". rewrite /auth_inv /auth_own.
    iDestruct "Hinv" as (t) "[>Hγa Hφ]".
    iModIntro. iExists t.
    iDestruct (own_valid_2 with "Hγa Hγf") as % [? ?]%auth_valid_discrete_2.
    iSplit; first done. iSplit; first done. iFrame. iIntros (u b) "[% Hφ]".
    iMod (own_update_2 with "Hγa Hγf") as "[Hγa Hγf]".
    { eapply auth_update; eassumption. }
    iModIntro. iFrame. iExists u. iFrame.
  Qed.

  Lemma auth_acc E γ a :
    ▷ auth_inv γ f φ ∗ auth_own γ a ={E}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E}=∗ ▷ auth_inv γ f φ ∗ auth_own γ b.
  Proof.
    rewrite auth_acc_strong. iIntros ">H !>". iDestruct "H" as (t) "(_&?&?)".
    iExists t. by iFrame.
  Qed.

  Lemma auth_open_strong E N γ a :
    ↑N ⊆ E →
    auth_ctx γ N f φ ∗ auth_own γ a ={E,E∖↑N}=∗ ∃ t,
      ⌜✓ (f t)⌝ ∗ ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E∖↑N,E}=∗ auth_own γ b.
  Proof.
    iIntros (?) "[#? Hγf]". rewrite /auth_ctx. iInv N as "Hinv" "Hclose".
    (* The following is essentially a very trivial composition of the accessors
       [auth_acc] and [inv_open] -- but since we don't have any good support
       for that currently, this gets more tedious than it should, with us having
       to unpack and repack various proofs.
       TODO: Make this mostly automatic, by supporting "opening accessors
       around accessors". *)
    iMod (auth_acc_strong with "[$Hinv $Hγf]") as (t) "(?&?&?&HclAuth)".
    iModIntro. iExists t. iFrame. iIntros (u b) "H".
    iMod ("HclAuth" $! u b with "H") as "(Hinv & ?)".
    by iMod ("Hclose" with "Hinv").
  Qed.

  Lemma auth_open E N γ a :
    ↑N ⊆ E →
    auth_ctx γ N f φ ∗ auth_own γ a ={E,E∖↑N}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E∖↑N,E}=∗ auth_own γ b.
  Proof.
    move=>?; rewrite auth_open_strong //. iIntros ">H !>".
    iDestruct "H" as (t) "(_&?&?&?)". iExists t. by iFrame.
  Qed.
End auth.
Arguments auth_open_strong {_ _ _} [_] {_} [_] _ _ _ _ _ _ _.
Arguments auth_open {_ _ _} [_] {_} [_] _ _ _ _ _ _ _.
End lib_auth.

Module weakestpre.	(* cf. ../program_logic/weakestpre.v *)
From iris.program_logic Require Import weakestpre.

Definition pbit_le (p1 p2 : pbit) : bool :=
  match p1, p2 with
  | progress, noprogress => false
  | _, _ => true
  end.

Instance: @PreOrder pbit pbit_le.
Proof.
  split; first by case. move=>p1 p2 p3. by case: p1; case: p2; case: p3.
Qed.

Section derived.
  Context `{irisG Λ Σ}.

  Lemma wp_pbit_mono p1 p2 E e Φ :
    pbit_le p1 p2 → WP e @ p2; E {{ Φ }} ⊢ WP e @ p1; E {{ Φ }}.
  Proof. case: p1; case: p2 => // _. exact: wp_forget_progress. Qed.
End derived.
End weakestpre.

Module ectx_language.	(* cf. ../program_logic/ectx_language.v *)
From iris.program_logic Require Import ectx_language.
Section ectx_language.
  Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
  Implicit Types (e : expr) (K : ectx).

  Lemma stuck_by_val K e σ e' σ' efs :
    is_Some (to_val (fill K e)) → ¬ head_step e σ e' σ' efs.
  Proof.
    intros Hv Hnv%val_stuck%(fill_not_val K). apply: is_Some_None.
    by rewrite Hnv in Hv.
  Qed.
End ectx_language.
End ectx_language.

Module ectx_lifting.	(* cf. ../program_logic/ectx_lifting.v *)
From iris.program_logic Require Import lifting ectx_lifting.
Section ectx_lifting.

  Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
  Context `{irisG (ectx_lang expr) Σ}.
  Implicit Types p : pbit.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  Definition head_progress (e : expr) (σ : state) :=
    is_Some(to_val e) ∨ ∃ K e', e = fill K e' ∧ head_reducible e' σ.

  Lemma progress_head_progress e σ :
    language.progress e σ → head_progress e σ.
  Proof.
    case=>[?|Hred]; first by left.
    right. move: Hred=> [] e' [] σ' [] efs [] K e1' e2' EQ EQ' Hstep. subst.
    exists K, e1'. split; first done. by exists e2', σ', efs.
  Qed.
  Hint Resolve progress_head_progress.

  Lemma wp_lift_head_stuck E Φ e :
    to_val e = None →
    (∀ σ, state_interp σ ={E,∅}=∗ ⌜¬ head_progress e σ⌝)
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_stuck; first done.
    iIntros (σ) "Hσ". iMod ("H" $! _ with "Hσ") as "%". iModIntro. by auto.
  Qed.

  Lemma wp_lift_pure_head_stuck `{Inhabited state} E Φ e :
    to_val e = None →
    (∀ K e1 σ1 e2 σ2 efs, e = fill K e1 → ¬ head_step e1 σ1 e2 σ2 efs) →
    WP e @ E ?{{ Φ }}%I.
  Proof.
    iIntros (Hnv Hnstep). iApply wp_lift_head_stuck; first done.
    iIntros (σ) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
    iModIntro. iPureIntro. case; first by rewrite Hnv; case.
    move=>[] K [] e1 [] Hfill [] e2 [] σ2 [] efs /= Hstep. exact: Hnstep.
  Qed.
End ectx_lifting.
End ectx_lifting.

Module adequacy.
From iris.base_logic Require Import big_op soundness.
From iris.program_logic Require Import adequacy.

Theorem wp_invariance Σ Λ `{invPreG Σ} p e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ},
     True ={⊤}=∗ ∃ stateI : state Λ → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI in
       stateI σ1 ∗ WP e @ p; ⊤ {{ v, True }} ∗ (stateI σ2 ={⊤,∅}=∗ ⌜φ⌝)) →
  rtc step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n ?]%rtc_nsteps.
  eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
  rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]".
  rewrite {1}fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
  iDestruct "Hwp" as (Istate) "(HIstate & Hwp & Hclose)".
  iModIntro. iNext. iApply (@wptp_invariance _ _ (IrisG _ _ Hinv Istate)); eauto.
  iFrame "Hw HE Hwp HIstate Hclose". by iApply big_sepL_nil.
Qed.
End adequacy.

Module ownp.
From iris.algebra Require Import auth.
From iris.program_logic Require Import ownp.
Import adequacy.

Theorem ownP_invariance Σ `{ownPPreG Λ Σ} p e σ1 t2 σ2 φ :
  (∀ `{ownPG Λ Σ},
    ownP σ1 ={⊤}=∗ WP e @ p; ⊤ {{ v, True }} ∗ |={⊤,∅}=> ∃ σ', ownP σ' ∧ ⌜φ σ'⌝) →
  rtc step ([e], σ1) (t2, σ2) →
  φ σ2.
Proof.
  intros Hwp Hsteps. eapply (wp_invariance Σ Λ p e σ1 t2 σ2 _)=> //.
  iIntros (?) "". iMod (own_alloc (● (Excl' (σ1 : leibnizC _)) ⋅ ◯ (Excl' σ1)))
    as (γσ) "[Hσ Hσf]"; first done.
  iExists (λ σ, own γσ (● (Excl' (σ:leibnizC _)))). iFrame "Hσ".
  iMod (Hwp (OwnPG _ _ _ _ γσ) with "[Hσf]") as "[$ H]"; first by rewrite /ownP.
  iIntros "!> Hσ". iMod "H" as (σ2') "[Hσf %]". rewrite/ownP.
  iDestruct (own_valid_2 with "Hσ Hσf")
    as %[->%Excl_included%leibniz_equiv _]%auth_valid_discrete_2; auto.
Qed.
End ownp.
