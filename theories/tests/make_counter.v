From iris.heap_lang Require Import heap adequacy.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

(** * Upward-capability counter client *)

Definition bump_closure (count : loc) : val :=
  rec: "incr" <> :=
    let: "n" := !count in
    let: "n'" := "n" + #1 in
    let: <> := count <- "n'" in
    "n'".

Definition bump_cap : val :=
  λ: "count",
    rec: "incr" <> :=
      let: "n" := !"count" in
      let: "n'" := "n" + #1 in
      let: <> := "count" <- "n'" in
      "n'".

Definition use_closure (f : val) : val :=
  rec: "use" <> :=
    let: "n" := f () in
    assert: (#0 < "n").

Definition use_cap : val :=
  λ: "f",
    rec: "use" <> :=
      let: "n" := "f" () in
      assert: (#0 < "n").

Definition decr_cap : val :=
  λ: "count",
    rec: "decr" <> :=
      let: "n" := !"count" in
      let: "n'" := "n" - #1 in
      let: <> := "count" <- "n'" in
      "n'".

Definition make_counter : val :=
  λ: <>,
    let: "count" := ref #0 in
    let: "incr" := bump_cap "count" in
    let: "decr" := decr_cap "count" in
    ("incr", "decr").

Definition checked_counter : expr :=
  let: "c" := make_counter () in
  let: "cUp" := Fst "c" in
  let: "use" := use_cap "cUp" in
  ("use", "cUp").

Section proof.
  Context `{heapG Σ}.
  Context (N : namespace) (HN : heapN ⊥ N).

  Definition counter_inv (count : loc) : iProp Σ :=
    (inv N (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z))%I.

  Lemma bump_cap_call_pos count :
    {{{ heap_ctx ∗ counter_inv count }}}
      (RecV "incr" <>
        (let: "n" := !count in
         let: "n'" := "n" + #1 in
         let: <> := count <- "n'" in
         "n'")) ()
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

  Lemma bump_closure_low count :
    heap_ctx ∗ counter_inv count ⊢
      low (RecV "incr" <>
        (let: "n" := !count in
         let: "n'" := "n" + #1 in
         let: <> := count <- "n'" in
         "n'")).
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
        (let: "n" := (rec: "incr" <> :=
          let: "n" := !count in
          let: "n'" := "n" + #1 in
          let: <> := count <- "n'" in
          "n'") () in
         assert: (#0 < "n"))).
  Proof.
    iIntros "#(Hh & Hinv)". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    wp_apply (wp_forget_progress progress).
    wp_apply (bump_cap_call_pos with "[$Hh $Hinv]").
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
    wp_lam. wp_let.
    wp_lam. wp_let.
    wp_let. wp_proj. wp_let.
    wp_lam. wp_let.
    iApply "HΦ". clear Φ. rewrite low_val /=. iNext.
    iSplitL.
    - by iApply (use_closure_low with "[$Hh $Hinv]").
    - by iApply (bump_closure_low with "[$Hh $Hinv]").
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
