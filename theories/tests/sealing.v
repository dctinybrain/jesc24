From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import sealing.
From iris.heap_lang.lib Require lock spin_lock.
From iris.heap_lang Require Import notation proofmode.
Import sealing.intf.

Local Hint Resolve to_of_val.

(** * Morris' protected interval manipulating routines *)
Section intervals_code.
  Context (SI : SealingImpl).

  Definition make_interval : val := λ: "s" "n1" "n2",
    seal SI "s" (if: "n1" ≤ "n2" then ("n1", "n2") else ("n2", "n1")).

  Definition unseal' : val := λ: "s" "x",
    let: "i" := unseal SI "s" "x" in
    assert: (Fst "i" ≤ Snd "i") ;; "i".

  Definition min : val := λ: "s" "x", Fst (unseal' "s" "x").
  Definition max : val := λ: "s" "x", Snd (unseal' "s" "x").
  Definition sum : val := λ: "s" "x" "y",
      let: "i" := unseal' "s" "x" in
      let: "j" := unseal' "s" "y" in
      seal SI "s" (Fst "i" + Fst "j", Snd "i" + Snd "j").

  Definition intervals : expr :=
    let: "s" := make_sealer_unsealer SI () in
    (make_interval "s", min "s", max "s", sum "s").
End intervals_code.

(**
	We prove a pair of triples for each operation, for use with
	high- and low-integrity code. For each pair, we could factor
	out a shared verification condition, but that's not worth
	doing with proofs this short.
*)
Section intervals_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.

  Definition is_interval' (n1 n2 : Z) (v : val) : iProp Σ :=
    (⌜v = (#n1, #n2)%V⌝ ∗ ⌜n1 ≤ n2⌝)%I.

  Global Instance is_interval'_persistent n1 n2 v :
    PersistentP (is_interval' n1 n2 v).
  Proof. apply _. Qed.

  Definition is_interval_sealer (γ : name S) (s : val) : iProp Σ :=
    is_sealer_unsealer S N γ s (λ v, (∃ n1 n2, is_interval' n1 n2 v))%I.

  Definition is_interval (γ : name S) (n1 n2 : Z) (v : val) : iProp Σ :=
    is_sealed S N γ (#n1, #n2)%V v.

  Lemma make_interval_spec p γ s :
    {{{ is_interval_sealer γ s }}} make_interval SI s @ p; ⊤
    {{{ f1, RET f1; ∀ p n1,
      {{{ True }}} f1 #n1 @ p; ⊤ {{{ f2, RET f2; ∀ p n2,
        {{{ True }}} f2 #n2 @ p; ⊤
        {{{ v, RET v; low v ∗ is_interval γ (Z.min n1 n2) (Z.max n1 n2) v }}}
      }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1) "!#". iIntros (Φ) "_ HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n2) "!#". iIntros (Φ) "_ HΦ". wp_lam.
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
    rewrite/is_interval/is_interval'. wp_op=>[?|/Z.lt_le_incl ?]; wp_if.
    - rewrite (Z.min_l n1) // (Z.max_r _ n2) //.
      wp_apply ("Hf" with "* [] [$HΦ]"). by iExists n1, n2; auto.
    - rewrite (Z.min_r _ n2) // (Z.max_l n1) //.
      wp_apply ("Hf" with "* [] [$HΦ]"). by iExists n2, n1; auto.
  Qed.

  Lemma make_interval_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} make_interval SI s @ p; ⊤
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. rewrite low_rec. iAlways. iNext.
    iIntros (v1 Φ) "#Hv1 HΦ". simpl_subst. wp_value.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
    iIntros (v2 Φ) "#Hv2 HΦ". simpl_subst.
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
    (* Inlining (derived) rules for stuck ≤. *)
    wp_bind (_ ≤ _)%E. case: (decide (is_int (of_val v1)))=>Hv1; last first.
    { iApply wp_stuck_bin_op=>//.
      case: v1 Hv1 => //. case=>//. rewrite/is_int. by naive_solver. }
    destruct (is_int_val _ Hv1) as (n1&->).
    case: (decide (is_int (of_val v2)))=>Hv2; last first.
    { iApply wp_stuck_bin_op=>//.
      case: v2 Hv2 => //. case=>//. rewrite/is_int. by naive_solver. }
    destruct (is_int_val _ Hv2) as (n2&->).
    (* Reasoning about the body. *)
    rewrite/is_interval/is_interval'. wp_op=>[?|/Z.lt_le_incl ?]; wp_if.
    - wp_apply ("Hf" with "* [] [HΦ]"). by iExists n1, n2; auto.
      by iIntros (?) "[? _]"; iApply "HΦ"; iFrame.
    - wp_apply ("Hf" with "* [] [HΦ]"). by iExists n2, n1; auto.
      by iIntros (?) "[? _]"; iApply "HΦ"; iFrame.
  Qed.

  Lemma unseal'_spec p γ s n1 n2 v' :
    {{{ is_interval_sealer γ s ∗ is_interval γ n1 n2 v' }}}
      unseal' SI s v' @ p; ⊤
    {{{ RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ". do 2!wp_lam.
    wp_apply (unseal_sealed_val with "[$Hs $Hv']").
      iDestruct 1 as (n'1 n'2) "[EQ %]". iDestruct "EQ" as %[=<-<-]. wp_let.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "[%]").
  Qed.

  Lemma unseal'_low_spec γ s v' :
    {{{ is_interval_sealer γ s ∗ low v' }}} unseal' SI s v'
    ?{{{ n1 n2, RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ". do 2!wp_lam.
    wp_apply (unseal_low_val with "[$Hs $Hv']"). iIntros (v) "#Hv". wp_let.
      iDestruct "Hv" as (n1 n2) "Hv".
      iDestruct (persistentP with "Hv") as ">[%%]". subst.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "[%]").
  Qed.

  Lemma min_spec p γ s :
    {{{ is_interval_sealer γ s }}} min SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET #n1; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
    wp_apply (unseal'_spec with "[$Hs $Hv']"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} min SI s @ p; ⊤ {{{ f, RET f;
      low f ∗ ∀ v', {{{ low v' }}} f v' ?{{{ n1, RET #n1; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    - rewrite low_rec. iAlways. iNext. iIntros (v' Φ) "Hv' HΦ". simpl_subst.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      iApply "HΦ". by simpl_low.
    - iIntros (v') "!#". iIntros (Φ) "Hv' HΦ". wp_lam.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      by iApply "HΦ".
  Qed.

  Lemma max_spec p γ s :
    {{{ is_interval_sealer γ s }}} max SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET #n2; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
    wp_apply (unseal'_spec with "[$Hs $Hv']"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma max_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} max SI s @ p; ⊤ {{{ f, RET f;
      low f ∗ ∀ v', {{{ low v' }}} f v' ?{{{ n2, RET #n2; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    - rewrite low_rec. iAlways. iNext. iIntros (v' Φ) "Hv' HΦ". simpl_subst.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      iApply "HΦ". by simpl_low.
    - iIntros (v') "!#". iIntros (Φ) "Hv' HΦ". wp_lam.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      by iApply "HΦ".
  Qed.

  Lemma sum_spec p γ s :
    {{{ is_interval_sealer γ s }}} sum SI s @ p; ⊤ {{{ f1, RET f1;
      ∀ p n1 n2 v1, {{{ is_interval γ n1 n2 v1 }}} f1 v1 @ p; ⊤ {{{ f2, RET f2;
        ∀ p n'1 n'2 v2, {{{ is_interval γ n'1 n'2 v2 }}} f2 v2 @ p; ⊤ {{{
          v', RET v'; low v' ∗ is_interval γ (n1+n'1) (n2+n'2) v'
        }}}
      }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v1) "!#". iIntros (Φ) "#Hv1 HΦ".
      wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n'1 n'2 v2) "!#". iIntros (Φ) "Hv2 HΦ".
      wp_lam.
    wp_apply (unseal'_spec with "[$Hs $Hv1]"). iIntros "%". wp_let.
    wp_apply (unseal'_spec with "[$Hs $Hv2]"). iIntros "%". wp_let.
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
      do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
    wp_apply ("Hf" with "* [] [$HΦ]"). iExists _, _. iSplitL; first done.
    iPureIntro. by lia.
  Qed.

  Lemma sum_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} sum SI s @ p; ⊤ {{{ f1, RET f1;
      low f1 ∗ ∀ v1, {{{ low v1 }}} f1 v1 ?{{{ f2, RET f2;
        low f2 ∗ ∀ v2, {{{ low v2 }}} f2 v2 ?{{{ n1 n2 v, RET v;
          is_interval γ n1 n2 v
        }}}
      }}}
    }}}.
  Proof.
    assert (Hbody :
      ∀ v1 v2,
      {{{ is_interval_sealer γ s ∗ low v1 ∗ low v2 }}}
        let: "i" := unseal' SI s v1 in let: "j" := unseal' SI s v2 in
        seal SI s (Fst "i" + Fst "j", Snd "i" + Snd "j")
      ?{{{ n1 n2 v, RET v; low v ∗ is_interval γ n1 n2 v }}}
    ).
    { iIntros (v1 v2 Φ) "#(Hs & Hv1 & Hv2) HΦ".
      wp_apply (unseal'_low_spec with "[$Hs $Hv1]").
        iIntros (n1 n2) "%". wp_let.
      wp_apply (unseal'_low_spec with "[$Hs $Hv2]").
        iIntros (n'1 n'2) "%". wp_let.
      wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
        do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
      wp_apply ("Hf" with "* [] [HΦ]").
      + iExists _, _. iSplit; first done. iPureIntro. by lia.
      + iIntros (?) "?". iApply "HΦ". by iFrame. }
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    { rewrite low_rec. iAlways. iNext. iIntros (v1 Φ) "#Hv1 HΦ".
        simpl_subst. wp_value.
      iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
        iIntros (v2 Φ) "#Hv2 HΦ". simpl_subst.
      wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[? _]".
      by iApply "HΦ". }
    iIntros (v1) "!#". iIntros (Φ) "#Hv1 HΦ". wp_lam.
    iApply "HΦ". clear Φ. iSplitL.
    { rewrite low_rec. iAlways. iNext. iIntros (v2 Φ) "#Hv2 HΦ".
        simpl_subst.
      wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[? _]".
      by iApply "HΦ". }
    iIntros (v2) "!#". iIntros (Φ) "#Hv2 HΦ". wp_lam.
    wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[_ ?]".
    by iApply "HΦ".
  Qed.

  Lemma intervals_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} intervals SI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/intervals.
    set φ : val → iProp Σ := λ v, (∃ n1 n2, is_interval' n1 n2 v)%I.
    wp_apply (make_sealer_unsealer_spec S N _ φ with "Hh");
      first done. iIntros (s γ) "#Hs". wp_let.
    wp_apply (make_interval_low_spec with "Hs"). iIntros (mk) "Hmk".
    wp_apply (min_low_spec with "Hs"). iIntros (min) "[Hmin _]".
    wp_apply (max_low_spec with "Hs"). iIntros (max) "[Hmax _]".
    wp_apply (sum_low_spec with "Hs"). iIntros (sum) "[Hsum _]".
      wp_value.
    iApply "HΦ". simpl_low. by iFrame.
  Qed.
End intervals_proof.

Section ClosedProofs.
  Import lock.

  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; proof.sealingΣ; spin_lock.lockΣ ].
  Let lock : LockImpl := spin_lock.spin.
  Let sealing : SealingImpl := code.sealing lock.
  Let intervals : expr := intervals sealing.

  Lemma intervals_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C intervals], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.spin_lock. set S := proof.sealing L.
    iApply (intervals_spec S N with "Hh"); auto with ndisj.
  Qed.
End ClosedProofs.

Print Assumptions intervals_safe.

(*
— signatures
	φ v asserts integrity of message v
		sign ≔ seal s	verify ≔ unseal s
For adversarial code:
	always(∀ v', φ v' -∗ low v') ⊢ low verify
For verified code:
	{φ v} sign v {v', low v'}
	{low v'} verify v' ?{v. φ v}

— encryption
	φ := low ensures that anyone can sign a message
		encrypt := seal s	decrypt := unseal s

For verified code:
	{low v} encrypt v {v', low v' ∗ is_ctext v v'}
	{is_ctext v v'} decrypt v' ?{RET v; True}

To support this interface, we want to define is_ctext ≔ is_sealed.
*)
