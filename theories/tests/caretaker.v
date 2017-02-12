From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import caretaker lock assume.
From iris.heap_lang.lib Require spin_lock.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import caretaker.

(** * Simple caretaker for locations *)
(**
	Revokable read/write access to a location with a reference
	monitor on writes.
*)

Section loc_ct_code.
  Context (CI : CaretakerImpl).

  Definition make_loc_ct : val := λ: "f" "l",
    let: "ct" := make_caretaker CI #() in
    let: "read" := wrap CI "ct" (λ: <>, ! "l") in
    let: "write" := wrap CI "ct" (λ: "v", "l" <- "f" "v") in
    ("ct", ("read", "write")).
End loc_ct_code.

Section loc_ct_proof.
  Context `{heapG Σ, CI : CaretakerImpl} (C : caretaker Σ).

  Definition is_refmon (f : val) (Ψ : val → iProp Σ) : iProp Σ :=
    (∀ v : val, {{{ low v }}} f v ?{{{ v', RET v'; low v' ∗ Ψ v' }}})%I.

  Lemma make_loc_ct_spec N f l Ψ :
    let R : iProp Σ := (∃ v, l ↦ v ∗ low v ∗ Ψ v)%I in
    heapN ⊥ N →
    {{{ heap_ctx ∗ is_refmon f Ψ }}} make_loc_ct CI f #l
    {{{ ct γ v, RET (ct, v);
      is_caretaker C N γ ct R ∗ enabled C γ false ∗ low v }}}.
  Proof.
    iIntros (R ? Φ) "#(Hh & Hf) HΦ". wp_lam. wp_lam.
    wp_apply (make_caretaker_spec _ _ _ R with "Hh"); first done.
      iIntros (ct γ) "(#Hct & Hoff)". wp_let.
    wp_bind (wrap _ _ _). rewrite of_val_rec.
    wp_apply (wrap_spec with "[$Hct]").
    { clear Φ. iIntros (arg). iAlways. iIntros (Φ) "[_ HR] HΦ".
        iDestruct "HR" as (v) "(Hl & #Hlow & HΨ)". wp_lam. wp_load.
      iApply "HΦ". iFrame "Hlow". iExists v. iFrame "Hl Hlow HΨ". }
    iIntros (read) "Hread". wp_let.
    wp_bind (wrap _ _ _). rewrite of_val_rec.
    wp_apply (wrap_spec with "[$Hct]").
    { clear Φ. iIntros (arg). iAlways. iIntros (Φ) "[Harg HR] HΦ".
        iDestruct "HR" as (v) "(Hl & #Hlow & HΨ)". wp_lam.
      wp_apply ("Hf" $! arg with "Harg"). iIntros (v') "[Hlow' HΨ']".
        wp_store.
      iApply "HΦ". iSplitR; first by simpl_low. iExists v'. by iFrame. }
    iIntros (write) "Hwrite". wp_let.
    iApply "HΦ". simpl_low. iFrame. iFrame "Hct".
  Qed.
End loc_ct_proof.

(** * Simple reference monitor: Write only even integers *)

Definition monitor : val := λ: "n", assume: even: "n" ;; "n".

Section monitor_proof.
  Context `{heapG Σ}.
  Implicit Types n : Z.
  Implicit Types v : val.

  Lemma monitor_spec v :
    {{{ True }}} monitor v ?{{{ n, RET v; ⌜v = #n⌝ ∗ ⌜Z.Even n⌝ }}}.
  Proof.
    iIntros (Φ) "HΦ". wp_lam.
    wp_apply wp_assume.
    case: (decide (is_int (of_val v)))=>Hint;
      last by wp_apply wp_stuck_even.
      destruct (is_int_val _ Hint) as (n&->).
    wp_op=>?.
    - iIntros "_ !>". wp_seq. by iApply "HΦ"; auto.
    - iIntros "%". by iExFalso.
  Qed.
End monitor_proof.

(** * Using the location caretaker *)

Section example_code.
  Context (CI : CaretakerImpl) (LI : LockImpl).
  Implicit Types n : Z.

  Definition example : expr :=
    let: "l" := ref #0 in
    let: "ct" := make_loc_ct CI monitor "l" in
    let: "loc" := Snd "ct" in
    let: "ct" := Fst "ct" in
    enable CI "ct" ;;
    let: "sync" := make_sync LI #() in
    let: "use" := "sync" (λ: <>,
      disable CI "ct" ;;
      assert: (even: (! "l")) ;;
      "l" <- #0 ;;
      enable CI "ct")
    in
    ("use", "loc").
End example_code.

Section example_proof.
  Context `{heapG Σ, CI : CaretakerImpl, LI : LockImpl}.
  Context (C : caretaker Σ) (L : lock Σ).
  Implicit Types n : Z.

  Lemma example_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} example CI LI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/example.
    wp_alloc l as "Hl". wp_let.
    set Ψ : val → iProp Σ := λ v, (∃ n, ⌜v = #n⌝ ∗ ⌜Z.Even n⌝)%I.
    wp_apply (make_loc_ct_spec _ _ _ _ Ψ with "[$Hh]"); first done.
    (** [is_refmon monitor Ψ] follows trivially from [monitor_spec]. *)
    { rewrite/is_refmon. iIntros (v) "!#". iIntros (Ψret) "_ Hret".
      wp_apply monitor_spec. iIntros (n) "#(EQ & EV)".
      iApply "Hret". iSplitR.
      + iDestruct "EQ" as %->. by simpl_low.
      + rewrite/Ψ. iExists n. by iFrame "EQ EV". }
    iIntros (ct γ loc) "(#Hct & Hoff & #Hloc)". wp_let.
      wp_proj. wp_let. wp_proj. wp_let.
    (** We need to turn the caretaker on with [l ↦ #0] twice. *)
    iAssert (
      {{{ enabled C γ false ∗ l ↦ #0 }}} enable CI ct
      {{{ RET #(); enabled C γ true }}}
    )%I as "#Hzero".
    { iAlways. clear Φ. iIntros (Φ) "[Hoff Hl] HΦ".
      wp_apply (enable_spec with "[$Hct $Hoff Hl] HΦ").
      iExists #0. iFrame "Hl". iSplit; first by simpl_low.
      rewrite/Ψ. iExists 0. iSplit; first done.
      iPureIntro. by apply Z.even_spec. }
    wp_apply ("Hzero" with "[$Hoff $Hl]"). iIntros "Hon". wp_seq.
    (* We need to stick the caretaker somewhere. We bury it in a lock. *)
    wp_apply (make_sync_spec L _ _ (enabled C γ true) with "[$Hh $Hon]"); first done.
      iIntros (sync) "#Hsync". wp_let. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψret) "Hon Hret".
    wp_apply (disable_spec with "[$Hct $Hon]").
      iIntros "(Hoff & HlocΨ)". wp_seq.
    wp_apply wp_assert.
      iDestruct "HlocΨ" as (v) "(Hl & Hlow & HΨ)". wp_load.
      iDestruct "HΨ" as (n) "(EQ & EV)".
      iDestruct "EQ" as %EQ. rewrite EQ.
    wp_op => Hparity; last first.
    { iExFalso. iDestruct "EV" as "%". iPureIntro.
      by apply (Z.Even_Odd_False n). }
    iSplit; first done. iNext. wp_seq. wp_store.
    wp_apply ("Hzero" with "[$Hoff $Hl]"). iIntros "Hon".
    iApply ("Hret" with "Hon"). wp_seq.
    iApply "HΦ". simpl_low. by iFrame "Hloc".
  Qed.
End example_proof.

Section ClosedProof.
  Import spin_lock blocking_caretaker.
  Let Σ : gFunctors := #[ heapΣ ; spin_lock.lockΣ ].
  Let example : expr := example (blocking spin) spin.

  Lemma example_safe C t2 σ2 :
    adv_ctx C →
    rtc step ([ctx_fill C example], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.
    set CT := blocking_caretaker L.
    set N := nroot .@ "example".
    iApply (example_spec CT L N with "Hh"); auto with ndisj.
  Qed.
End ClosedProof.

Print Assumptions example_safe.
