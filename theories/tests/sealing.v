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

Section intervals_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).
  Implicit Types f v : val.
  Implicit Types n : Z.

  Definition is_interval (v : val) : iProp Σ :=
    (∃ n1 n2, ⌜v = (#n1, #n2)%V⌝ ∗ ⌜n1 ≤ n2⌝)%I.

  Global Instance is_interval_persistent v : PersistentP (is_interval v).
  Proof. apply _. Qed.

STOP. Reconsider these interfaces.

  Lemma make_interval_spec N γ s :
    {{{ is_sealer_unsealer S N γ s is_interval }}}
      make_interval SI s
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
    iIntros (v1 Φ) "#Hv1 HΦ". simpl_subst. wp_value.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
    iIntros (v2 Φ) "#Hv2 HΦ". simpl_subst.
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
    (* Inlining (derived) rules for stuck ≤. *)
    wp_bind (_ ≤ _)%E.
    case: (decide (is_int (of_val v1)))=>Hv1; last first.
    { iApply wp_stuck_bin_op=>//.
      case: v1 Hv1 => //. case=>//. rewrite/is_int. by naive_solver. }
    destruct (is_int_val _ Hv1) as (n1&->).
    case: (decide (is_int (of_val v2)))=>Hv2; last first.
    { iApply wp_stuck_bin_op=>//.
      case: v2 Hv2 => //. case=>//. rewrite/is_int. by naive_solver. }
    destruct (is_int_val _ Hv2) as (n2&->).
    wp_op=>Hle; wp_if.
    - wp_apply ("Hf" with "* [] [$HΦ]"). iExists n1, n2. by iSplitL.
    - wp_apply ("Hf" with "* [] [$HΦ]"). iExists n2, n1.
      iSplitL; first done. iPureIntro. exact: Z.lt_le_incl.
  Qed.

  Lemma unseal'_spec N γ s v' :
    {{{ is_sealer_unsealer S N γ s is_interval ∗ low v' }}} unseal' SI s v'
    ?{{{ v, RET v; is_interval v }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ". do 2!wp_lam.
    wp_apply (unseal_val with "[$Hs $Hv']"). iIntros (v) "#Hv". wp_let.
      iDestruct (persistentP with "Hv") as (n1 n2) ">[%%]". subst.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma min_spec N γ s :
    {{{ is_sealer_unsealer S N γ s is_interval }}} min SI s {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (unseal'_spec with "[$Hs $Hv']"). iIntros (v) "Hv".
      iDestruct "Hv" as (n1 n2) "[%%]". subst. wp_proj.
    iApply "HΦ". by simpl_low.
  Qed.

  Lemma max_spec N γ s :
    {{{ is_sealer_unsealer S N γ s is_interval }}} max SI s {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (unseal'_spec with "[$Hs $Hv']"). iIntros (v) "Hv".
      iDestruct "Hv" as (n1 n2) "[%%]". subst. wp_proj.
    iApply "HΦ". by simpl_low.
  Qed.

  Lemma sum_spec N γ s :
    {{{ is_sealer_unsealer S N γ s is_interval }}} sum SI s {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v1 Φ) "#Hv1 HΦ". simpl_subst. wp_value.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v2 Φ) "#Hv2 HΦ". simpl_subst.
    wp_apply (unseal'_spec with "[$Hs $Hv1]"). iIntros (?) "Hi1".
      iDestruct "Hi1" as (lo1 hi1) "[%%]". subst. wp_let.
    wp_apply (unseal'_spec with "[$Hs $Hv2]"). iIntros (?) "Hi2".
      iDestruct "Hi2" as (lo2 hi2) "[%%]". subst. wp_let.
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
      do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
    wp_apply ("Hf" with "* [] [$HΦ]"). iExists _, _. iSplit; first done.
    iPureIntro. by lia.
  Qed.

  Lemma intervals_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} intervals SI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/intervals.
    wp_apply (make_sealer_unsealer_spec S N _ is_interval with "Hh");
      first done. iIntros (s γ) "#Hs". wp_let.
    wp_apply (make_interval_spec with "Hs"). iIntros (mk) "Hmk".
    wp_apply (min_spec with "Hs"). iIntros (min) "Hmin".
    wp_apply (max_spec with "Hs"). iIntros (max) "Hmax".
    wp_apply (sum_spec with "Hs"). iIntros (sum) "Hsum". wp_value.
    iApply "HΦ". simpl_low. by iFrame.
  Qed.
End intervals_proof.

Section ClosedProofs.
  Import lock.

  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; spin_lock.lockΣ ].
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
	φ v asserts integrity of message v
		sign ≔ seal s	verify ≔ unseal s
For adversarial code:
	always(∀ v', φ v' -∗ low v') ⊢ low verify
For verified code:
	{φ v} sign v {v', low v'}
	{low v'} verify v' ?{v. φ v}

—
	φ := low ensures that anyone can sign a message

		encrypt := seal s	decrypt := unseal s

For verified code:
	{low v} encrypt v {v', low v' ∗ is_ctext v v'}
	{is_ctext v v'} decrypt v' ?{RET v; True}	(* this should require fresh *)

To support this interface, we want to extend
the sealing interface with is_sealed v v' and define is_ctext ≔ is_sealed.
We probably want [is_sealed v v'] anyway, since we can hang invariants
off v.
*)


(*


  Definition sealer_res (l : loc) (γ : gname) : iProp Σ :=
    (∃ v log, l ↦ v ∗ is_env M v log ∗ own γ (● to_log log))%I.

  Definition is_ptext (γ : gname) (v : val) : iProp Σ :=
    (∃ k, own γ (◯ {[k, v]}))%I.
  Definition is_ctext (γ : gname) (v c : val) : iProp Σ :=
    (∀ k : loc, {{{ True }}} c #k {{{ RET #(); is_ptext γ v }}})%I.
  Definition is_sealer (γ : gname) (seal : val) : iProp Σ :=
    (low seal ∗
     ∀ v, {{{ True }}} seal v {{{ c, RET c; is_ctext γ v c}}})%I.
  Definition is_unsealer (γ : gname) (unseal : val) : iProp Σ :=
    (∀ c : val, {{{ low c }}} unseal c ?{{{ v, RET v; is_ptext γ v }}})%I.

  (** Ghost moves *)

  Lemma to_log_obs γ k v log :
    (k, v) ∈ log →
    own γ (● to_log log) ==∗ own γ (● to_log log) ∗ own γ (◯ {[k, v]}).
  Proof.
    move=>?. rewrite -own_op. apply own_update.
    apply auth_frag_alloc; try apply _.
    apply gset_included, elem_of_subseteq_singleton.
    rewrite/to_log. by induction log; set_solver.
  Qed.

  Lemma to_log_cons γ k v log log' :
    log' = (k, v) :: log →
    own γ (● to_log log) ==∗ own γ (● to_log log') ∗ own γ (◯ {[k, v]}).
  Proof.
    move=>->. rewrite -(own_mono _ (◯ to_log ((k, v) :: log)) (◯ {[k, v]})).
    - rewrite -own_op.
      apply own_update, auth_update_alloc, gset_local_update.
      by set_solver.
    - apply auth_included. split; first done. simpl.
      apply gset_included. by set_solver.
  Qed.

  (** Structure *)

  Global Instance is_ptext_persistent γ v : PersistentP (is_ptext γ v).
  Proof. apply _. Qed.
  Global Instance is_ptext_timeless γ v : TimelessP (is_ptext γ v).
  Proof. apply _. Qed.
  Global Instance is_sealer_persistent γ v : PersistentP (is_sealer γ v).
  Proof. apply _. Qed.
  Global Instance is_unsealer_persistent γ v : PersistentP (is_unsealer γ v).
  Proof. apply _. Qed.
  Global Instance is_ctext_persistent γ v c : PersistentP (is_ctext γ v c).
  Proof. apply _. Qed.

  (** Main proof *)

  Lemma sealer_low γ seal : is_sealer γ seal -∗ low seal.
  Proof. by iIntros "(?&_)". Qed.

  Lemma sealer_spec γ seal v :
    {{{ is_sealer γ seal }}} seal v {{{ c, RET c; is_ctext γ v c }}}.
  Proof.
    iIntros (Φ) "(_&Hseal) HΦ". rewrite/is_sealer.
    by wp_apply ("Hseal" $! v with "[] [$HΦ]").
  Qed.

  Lemma ctext_low γ v c : is_ctext γ v c -∗ low c.
  Admitted.

  Lemma ctext_spec γ v c (k : loc) :
    {{{ is_ctext γ v c }}} c #k {{{ RET #(); is_ptext γ v }}}.
  Admitted.

  Lemma unsealer_spec γ unseal (c : val) :
    {{{ is_unsealer γ unseal ∗ low c }}} unseal c ?{{{ v, RET v; is_ptext γ v }}}.
  Admitted.

  Lemma make_pair_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_pair L M #()
    {{{ v1 v2 γ, RET (v1, v2); is_sealer γ v1 ∗ is_unsealer γ v2 }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam.
    wp_alloc l as "Hl". iDestruct (empty_spec _ M) as "Henv". wp_let.
    iMod (own_alloc (● to_log [])) as (γ) "Hγa";
      first exact: auth_auth_valid.
    set res := (sealer_res l γ)%I. iAssert res with "[Hl Henv Hγa]" as "Hres".
    { iExists (empty M), []. iFrame. by iFrame "#". }
    wp_apply (make_sync_spec _ _ _ res with "[$Hh $Hres]"); first done.
      iIntros (sync) "#Hsync". wp_let. wp_let. wp_let.
    iApply ("HΦ" $! _ _ γ). iClear (Φ) "Henv". iSplitL.
    (* Sealer *)
    - rewrite/is_sealer. iSplitL.
(* PDS: The sealer, and ciphertexts are low.
We're baking this into the sealer proof because
we didn't want to state is_sealer in terms of β reduced functions.
*)
      + rewrite low_val. iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst.
          wp_value.
        iApply "HΦ". clear Φ.
        rewrite (low_val (LamV _ _)). iAlways. iNext. iIntros (k Φ) "#Hk HΦ".
          simpl_subst.
        wp_typecast Hloc.
        wp_value. wp_lam.

      iIntros (v) "!#". iIntros (Φ) "_ HΦ". wp_lam.
      iApply "HΦ". clear Φ.
      iIntros (k) "!#". iIntros (Φ) "_ HΦ". wp_lam.
      wp_typecast Hloc; last by exfalso; apply Hloc; exists k.
      wp_match.
      rewrite/is_sync. wp_apply ("Hsync" with "[%]"). iClear "Hsync".
        iIntros (Ψ) "Hres HΨ".
        iDestruct "Hres" as (vlog log) "(Hl & #Henv & Hγa)".
      wp_load.
      wp_apply (insert_spec with "[$Henv]"). iIntros (vlog') "#Henv'".
      rewrite -wp_fupd. wp_store.
      iMod (to_log_cons _ k v with "Hγa") as "[Hγa Hγf]"; first done.
      iModIntro. iApply ("HΨ" with "[Hl Henv' Hγa]").
      { iExists vlog', _. iFrame. by iFrame "#". }
      iApply "HΦ". by iExists k.
    (* Unsealer *)
    - iIntros (c) "!#". iIntros (Φ) "#Hc HΦ". wp_lam.
      wp_alloc k as "Hk". wp_let.
      iMod (heap_mark_low with "[$Hh] [$Hk] []") as "Hk";
        [done | by simpl_low |].
      wp_apply (wp_on_val_app _ _ (#k) with "[$Hc Hk]");
        first by simpl_on_val. iIntros (v0) "_". wp_seq. clear v0.
      rewrite/is_sync. wp_apply ("Hsync" with "[%]"). iClear "Hsync".
        iIntros (Ψ) "Hres HΨ".
        iDestruct "Hres" as (vlog log) "(Hl & #Henv & Hγa)".
      wp_load. rewrite -wp_fupd.
      wp_apply (lookup_spec with "[$Henv]"). iIntros (x) "%".
      iMod (to_log_obs with "Hγa") as "[Hγa Hγf]"; first done.
      iModIntro. iApply ("HΨ" with "[Hl Henv Hγa]").
      { iExists vlog, log. iFrame. by iFrame "#". }
      iApply "HΦ". by iExists k.
  Qed.
End proof.
*)
