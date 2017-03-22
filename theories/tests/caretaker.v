From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import caretaker.
From iris.heap_lang.lib Require Import monitor lock.
From iris.heap_lang.lib Require spin_lock.
From iris.tests Require Import even.
From iris.heap_lang Require Import proofmode notation.
Import caretaker.

(** * Caretaker for locations *)
(**
	Revokable read/write access to a location with
	reference monitors on reads and writes.
*)

Section loc_ct_code.
  Context (CI : CaretakerImpl).

  Definition make_loc_ct : val := λ: "rmon" "wmon" "l",
    let: "ct" := make_caretaker CI () in
    let: "read" := wrap CI "ct" (λ: <>, "rmon" (! "l")) in
    let: "write" := wrap CI "ct" (λ: "v", "l" <- "wmon" "v") in
    ("ct", ("read", "write")).
End loc_ct_code.

Section loc_ct_proof.
  Context `{heapG Σ, CI : CaretakerImpl} (C : caretaker Σ).

  Definition is_rmon (p1 : pbit) (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
    is_mon p1 v Ψ (λ v1 v2, (lowval v2 ∗ Ψ v1)%I).

  Definition is_wmon (p2 : pbit) (v : val) (Ψ : val → iProp Σ) : iProp Σ :=
    is_monP p2 v lowval Ψ.

  Let ct_res (l : loc) (Ψ : val → iProp Σ) : iProp Σ := (∃ v, l ↦ v ∗ Ψ v)%I.

  Definition is_loc_ct (N : namespace) (γ : name C)
      (ct : val) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
    is_caretaker C N γ ct $ ct_res l Ψ.

  (** Bookkeeping. *)
  Lemma rmon_triple rmon p1 Ψ :
    is_rmon p1 rmon Ψ ⊣⊢
    (∀ v1 : val, {{{ Ψ v1 }}} rmon v1 @ p1; ⊤ {{{ v2, RET v2; low v2 ∗ Ψ v1 }}})%I.
  Proof. by []. Qed.

  Lemma wmon_triple wmon p2 Ψ :
    is_wmon p2 wmon Ψ ⊣⊢
    (∀ v1 : val, {{{ low v1 }}} wmon v1 @ p2; ⊤ {{{ v2, RET v2; Ψ v2 }}})%I.
  Proof. by []. Qed.

  Lemma can_wrap_loc_ct_read p1 N γ ct l r Ψ :
    heap_ctx -∗
    is_loc_ct N γ ct l Ψ -∗
    is_rmon p1 r Ψ -∗
    can_wrap p1 (LamV <> (r (! l)%E)) (ct_res l Ψ).
  Proof.
    iIntros "#Hh #Hct #Hr". iIntros (arg) "!#". iIntros (Φ) "[_ HR] HΦ".
      iDestruct "HR" as (v1) "(Hl & Hv1)". wp_lam. wp_load.
      rewrite rmon_triple.
    wp_apply ("Hr" $! v1 with "[$Hv1]"). iIntros (v2) "[Hlow2 Hv1]".
    iApply "HΦ". iFrame "Hlow2". iExists v1. by iFrame.
  Qed.

  Lemma can_wrap_loc_ct_write p2 N γ ct l w Ψ :
    heap_ctx -∗
    is_loc_ct N γ ct l Ψ -∗
    is_wmon p2 w Ψ -∗
    can_wrap p2 (LamV "v" (l <- w "v")) (ct_res l Ψ).
  Proof.
    iIntros "#Hh #Hct #Hw". iIntros (v1) "!#". iIntros (Φ) "[Hv1 HR] HΦ".
      wp_lam. rewrite wmon_triple.
    wp_apply ("Hw" $! v1 with "Hv1"). iIntros (v2) "HΨ2".
      iDestruct "HR" as (v0) "(Hl & _)". wp_store.
    iApply "HΦ". iSplitR; first by simpl_low. iExists v2. by iFrame.
  Qed.

  (** Specialize the caretaker interface. *)

 Lemma loc_ct_enable N γ ct l v p Ψ :
    {{{ is_loc_ct N γ ct l Ψ ∗ enabled C γ false ∗ l ↦ v ∗ Ψ v }}}
      enable CI ct @ p; ⊤
    {{{ RET (); enabled C γ true }}}.
  Proof.
    iIntros (Φ) "(#Hct & Hoff & Hl & Hv) HΦ".
    wp_apply (enable_spec with "[$Hct $Hoff Hl Hv] HΦ").
    iExists v. by iFrame.
  Qed.

 Lemma loc_ct_disable N γ ct l p Ψ :
    {{{ is_loc_ct N γ ct l Ψ ∗ enabled C γ true }}}
      disable CI ct @ p; ⊤
    {{{ v, RET (); enabled C γ false ∗ l ↦ v ∗ Ψ v }}}.
  Proof.
    iIntros (Φ) "(#Hct & Hon) HΦ".
    wp_apply (disable_spec _ _ _ _ _ (ct_res l Ψ) with "[$Hct $Hon]").
      iIntros "[Hoff HR]". iDestruct "HR" as (v) "(Hl & Hv)".
    by iApply ("HΦ" $! v with "[$Hoff $Hl $Hv]").
  Qed.

  Lemma make_loc_ct_spec N r w l Ψ p1 p2 :
    heapN ⊥ N →
    {{{ heap_ctx ∗ is_rmon p1 r Ψ ∗ is_wmon p2 w Ψ }}}
      make_loc_ct CI r w l
    {{{ ct γ v, RET (ct, v);
      is_loc_ct N γ ct l Ψ ∗ enabled C γ false ∗ low v }}}.
  Proof.
    iIntros (? Φ) "#(Hh & Hr & Hw) HΦ". wp_lam. wp_lam. wp_lam.
    wp_apply (make_caretaker_spec C _ _ (ct_res l Ψ) with "Hh");
      first done. iIntros (ct γ) "(#Hct & Hoff)". wp_let.
    wp_bind (wrap _ _ _). rewrite of_val_rec.
    wp_apply (wrap_spec with "[$Hct]").
    - by iApply (can_wrap_loc_ct_read with "Hh Hct Hr").
    iIntros (read) "Hread". wp_let.
    wp_bind (wrap _ _ _). rewrite of_val_rec.
    wp_apply (wrap_spec with "[$Hct]").
    - by iApply (can_wrap_loc_ct_write with "Hh Hct Hw").
    iIntros (write) "Hwrite". wp_let.
    iApply "HΦ". simpl_low. by iFrame "Hct Hoff Hread Hwrite".
  Qed.
End loc_ct_proof.

(** * Location caretaker client *)
(**
	Revokable read/write access to an even integer.
*)

Section even_code.
  Context (CI : CaretakerImpl) (LI : LockImpl).
  Implicit Types n : Z.

  Definition even : expr :=
    let: "l" := ref #0 in
    let: "ct" := make_loc_ct CI assert_even assume_even "l" in
    let: "loc" := Snd "ct" in
    let: "ct" := Fst "ct" in
    enable CI "ct" ;;
    let: "sync" := make_sync LI () in
    let: "use" := "sync" (λ: <>,
      disable CI "ct" ;;
      assert: (even: (! "l")) ;;
      "l" <- #1 ;;	(* i.e., with wrappers off, we can do as we like *)
      "l" <- #0 ;;
      enable CI "ct")
    in
    ("use", "loc").
End even_code.

Section even_proof.
  Context `{heapG Σ, CI : CaretakerImpl, LI : LockImpl}.
  Context (C : caretaker Σ) (L : lock Σ).
  Implicit Types n : Z.

  (* We need to stick the caretaker somewhere. We use the lock. *)
  Let lock_res (γ : name C) : iProp Σ :=
    enabled C γ true.

  (* We turn the caretaker on with [l ↦ #0] twice. *)
  Lemma enable_zero N γ ct l :
    {{{ is_loc_ct C N γ ct l is_even ∗ enabled C γ false ∗ l ↦ #0 }}}
      enable CI ct
    {{{ RET (); enabled C γ true }}}.
  Proof.
    iIntros (Φ) "(#Hct & Hoff & Hl) HΦ".
    wp_apply (loc_ct_enable with "[$Hct $Hoff $Hl] HΦ").
    iExists 0. iSplit; first done. iPureIntro. by apply Z.even_spec.
  Qed.

  Lemma even_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} even CI LI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/even.
    wp_alloc l as "Hl". wp_let.
    wp_apply (make_loc_ct_spec C _ _ _ _ is_even with "[$Hh]");
      [done | iSplitL; clear Φ |].
    - iIntros (v) "!#". iIntros (Φ) "#Hv HΦ".
      wp_apply (assert_even_spec with "Hv"). iIntros "_".
      iApply "HΦ". rewrite -low_val_eq -is_even_low. by iFrame "Hv".
    - iIntros (v) "!#". iIntros (Φ) "_ HΦ".
      wp_apply assume_even_spec. iIntros "Hv".
      iApply "HΦ". by iFrame.
    iIntros (ct γ loc) "(#Hct & Hoff & #Hloc)". wp_let.
      wp_proj. wp_let. wp_proj. wp_let.
    wp_apply (enable_zero with "[$Hct $Hoff $Hl]").
      iIntros "Hon". wp_seq.
    wp_apply (make_sync_spec L _ _ (lock_res γ) with "[$Hh $Hon]");
      first done. iIntros (sync) "#Hsync". wp_let. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψret) "Hon Hret".
    wp_apply (loc_ct_disable with "[$Hct $Hon]").
      iIntros (v) "(Hoff & Hl & Hv)". wp_seq.
    wp_apply wp_assert. wp_load.
      iDestruct "Hv" as (n) "(EQ & EV)".
      iDestruct "EQ" as %EQ. rewrite EQ.
    wp_op => Hparity; last first.
    { iExFalso. iDestruct "EV" as "%". iPureIntro.
      by apply (Z.Even_Odd_False n). }
    iSplit; first done. iNext. wp_seq. wp_store. wp_store.
    wp_apply (enable_zero with "[$Hct $Hoff $Hl]"). iIntros "Hon".
    iApply ("Hret" with "Hon"). wp_seq.
    iApply "HΦ". simpl_low. by iFrame "Hloc".
  Qed.
End even_proof.

Section ClosedProof.
  Import spin_lock blocking_caretaker.
  Let Σ : gFunctors := #[ heapΣ ; spin_lock.lockΣ ].
  Let example : expr := even (blocking spin) spin.

  Lemma even_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C example], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.
    set CT := blocking_caretaker L.
    set N := nroot .@ "example".
    iApply (even_spec CT L N with "Hh"); auto with ndisj.
  Qed.
End ClosedProof.

Print Assumptions even_safe.
