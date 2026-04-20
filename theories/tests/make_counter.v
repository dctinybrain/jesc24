From iris.heap_lang Require Import heap adequacy.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

(** * Upward-capability counter client *)

Definition op_assign (op : bin_op) (lhs rhs : expr) : expr :=
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store lhs (Var "__assign_new"))))
        (BinOp op (Var "__assign_old") rhs)))
    (Load lhs).

(* The old Closed instance does not unfold op_assign through rec bodies,
   so keep the update notations expanded at parse time. *)
Local Notation "e1 += e2" := (
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store e1%E (Var "__assign_new"))))
        (BinOp PlusOp (Var "__assign_old") e2%E)))
    (Load e1%E)
)
  (at level 80, format "e1  +=  e2") : expr_scope.

Local Notation "e1 -= e2" := (
  App
    (Lam (BNamed "__assign_old")
      (App
        (Lam (BNamed "__assign_new")
          (App
            (Lam BAnon (Var "__assign_new"))
            (Store e1%E (Var "__assign_new"))))
        (BinOp MinusOp (Var "__assign_old") e2%E)))
    (Load e1%E)
)
  (at level 80, format "e1  -=  e2") : expr_scope.

Definition make_counter : val :=
  λ: <>,
    let: "count" := ref #0 in
    let: "incr" := (λ: "count", rec: "incr" <> := "count" += #1) "count" in
    let: "decr" := (λ: "count", rec: "decr" <> := "count" -= #1) "count" in
    ("incr", "decr").

Definition checked_counter : expr :=
  let: "c" := make_counter () in
  let: "cUp" := Fst "c" in
  let: "use" := (λ: "cUp",
    rec: "use" <> :=
      let: "n" := "cUp" () in
      assert: (#0 < "n")) "cUp" in
  ("use", "cUp").

Section proof.
  Context `{heapG Σ}.
  Context (N : namespace) (HN : heapN ⊥ N).

  Definition counter_inv (count : loc) : iProp Σ :=
    (inv N (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z))%I.

  Lemma incr_call_pos count :
    {{{ heap_ctx ∗ counter_inv count }}}
      (RecV "incr" <> (count += #1)) ()
    {{{ v, RET v; ∃ z : Z, ⌜v = #z⌝ ∗ ⌜0 < z⌝ }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hinv) HΦ".
    wp_rec.
    wp_bind (! count)%E.
    iInv N as (z) ">Hz" "Hclose".
    iDestruct "Hz" as "[Hz Hcount]".
    iDestruct "Hz" as %Hz.
    wp_load.
    iMod ("Hclose" with "[Hcount]") as "_".
    { iNext. iExists z. iSplit; first done. iFrame "Hcount". }
    iModIntro.
    wp_let. wp_op. wp_let.
    wp_bind (count <- #(z + 1))%E.
    iInv N as (z') ">Hz'" "Hclose".
    iDestruct "Hz'" as "[Hz' Hcount]".
    iDestruct "Hz'" as %Hz'.
    wp_store.
    iMod ("Hclose" with "[Hcount]") as "_".
    { iNext. iExists (z + 1). iSplit.
      - iPureIntro. lia.
      - iFrame "Hcount". }
    iModIntro.
    wp_seq.
    iApply "HΦ". iExists (z + 1). iSplit.
    - done.
    - iPureIntro. lia.
  Qed.

  Lemma incr_closure_low count :
    heap_ctx ∗ counter_inv count ⊢
      low (RecV "incr" <> (count += #1)).
  Proof.
    iIntros "#(Hh & Hinv)". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    wp_apply (wp_forget_progress progress).
    wp_bind (! count)%E.
    iInv N as (z) ">Hz" "Hclose".
    iDestruct "Hz" as "[Hz Hcount]".
    iDestruct "Hz" as %Hz.
    wp_load.
    iMod ("Hclose" with "[Hcount]") as "_".
    { iNext. iExists z. iSplit; first done. iFrame "Hcount". }
    iModIntro.
    wp_let. wp_op. wp_let.
    wp_bind (count <- #(z + 1))%E.
    iInv N as (z') ">Hz'" "Hclose".
    iDestruct "Hz'" as "[Hz' Hcount]".
    iDestruct "Hz'" as %Hz'.
    wp_store.
    iMod ("Hclose" with "[Hcount]") as "_".
    { iNext. iExists (z + 1). iSplit.
      - iPureIntro. lia.
      - iFrame "Hcount". }
    iModIntro.
    wp_seq.
    iApply "HΦ". by simpl_low.
  Qed.

  Lemma use_closure_low count :
    heap_ctx ∗ counter_inv count ⊢
      low (RecV "use" <>
        (let: "n" := (rec: "incr" <> := count += #1) () in
         assert: (#0 < "n"))).
  Proof.
    iIntros "#(Hh & Hinv)". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    wp_apply (wp_forget_progress progress).
    wp_apply (incr_call_pos with "[$Hh $Hinv]").
    iIntros (v) "Hv".
    iDestruct "Hv" as (z) "Hv".
    iDestruct "Hv" as "[Hv Hpos]".
    iDestruct "Hv" as %Hv.
    iDestruct "Hpos" as %Hpos.
    subst v.
    wp_let.
    wp_apply wp_assert. wp_op=>?; last by exfalso; lia.
    iSplit; first done.
    by iApply "HΦ"; simpl_low.
  Qed.

  Lemma checked_counter_spec :
    {{{ heap_ctx }}} checked_counter {{{ v, RET v; low v }}}.
  Proof.
    iIntros (Φ) "#Hh HΦ". rewrite /checked_counter /make_counter.
    wp_lam.
    wp_alloc count as "Hcount". wp_let.
    iMod (inv_alloc N _ (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z)%I with "[Hcount]") as "#Hinv".
    { iNext. iExists 0. iFrame. done. }
    wp_let.
    wp_let.
    wp_let.
    wp_let.
    wp_let.
    wp_proj. wp_let.
    wp_let.
    wp_let.
    iApply "HΦ". clear Φ. rewrite low_val /=. iNext.
    iSplitL.
    - by iApply (use_closure_low with "[$Hh $Hinv]").
    - by iApply (incr_closure_low with "[$Hh $Hinv]").
  Qed.
End proof.

Lemma checked_counter_safe C t2 σ2 :
  AdvCtx C →
  rtc step ([ctx_fill C checked_counter], good_state ∅) (t2, σ2) →
  is_good σ2.
Proof.
  set Σ : gFunctors := #[heapΣ].
  set N : namespace := nroot .@ "checked_counter".
  move=>??. eapply (robust_safety Σ); try done.
  { naive_solver eauto using is_closed_of_val. }
  iIntros (?) "Hh". wp_apply (checked_counter_spec N with "Hh"); auto with ndisj.
Qed.

Print Assumptions checked_counter_safe.
