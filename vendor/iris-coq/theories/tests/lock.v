From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import lock.
From iris.heap_lang.lib Require spin_lock.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

(**
	Ensure we can still apply metatheorems to code using locks.
*)

Definition ignore_lock {LI : LockImpl} : expr :=
  let: "lk" := newlock () in ().

Section proof.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ).

  Lemma ignore_lock_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} ignore_lock {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/ignore_lock.
    wp_apply (newlock_spec L _ _ True%I with "[$Hh]"); first done.
      iIntros (lk γ) "Hlk". wp_let.
    iApply "HΦ". by simpl_low.
  Qed.
End proof.

Section ClosedProof.
  Let lock : LockImpl := spin_lock.code.
  Let ignore_lock : expr := @ignore_lock lock.

  Lemma ignore_lock_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C $ ignore_lock], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    set Σ : gFunctors := #[ heapΣ ; spin_lock.lockΣ ].
    set N : namespace := nroot .@ "example".
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (?) "Hh".
    set L := spin_lock.proof.
    iApply (ignore_lock_spec L N with "Hh"); auto with ndisj.
  Qed.
End ClosedProof.
Print Assumptions ignore_lock_safe.
