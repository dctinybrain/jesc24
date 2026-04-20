From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import counter.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

(** * Upward-capability counter client *)

Definition bump_closure (l : loc) : val :=
  rec: "bump" <> := incr l ;; read l.

Definition bump_cap : val :=
  λ: "l", rec: "bump" <> := incr "l" ;; read "l".

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
  λ: "l",
    rec: "decr" <> :=
      let: "n" := !"l" in
      let: <> := "l" <- ("n" - #1) in
      !"l".

Definition make_counter : val :=
  λ: <>,
    let: "l" := newcounter () in
    let: "incr" := bump_cap "l" in
    let: "decr" := decr_cap "l" in
    ("incr", "decr").

Definition checked_counter : expr :=
  let: "c" := make_counter () in
  let: "cUp" := Fst "c" in
  let: "use" := use_cap "cUp" in
  ("use", "cUp").

Section proof.
  Context `{!heapG Σ, !mcounterG Σ}.
  Context (N : namespace) (HN : heapN ⊥ N).

  Lemma bump_cap_call_pos l :
    {{{ mcounter N l 0 }}} (RecV "bump" <> (incr l ;; read l)) ()
    {{{ v, RET v; ∃ n : nat, ⌜v = #n⌝ ∗ ⌜(0 < n)%nat⌝ ∗ mcounter N l n }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_rec.
    wp_apply (incr_mono_spec N l 0 with "Hc").
    iIntros "Hc".
    wp_seq.
    wp_apply (read_mono_spec N l 1 with "Hc").
    iIntros (n) "H".
    iDestruct "H" as "[Hle Hc]".
    iDestruct "Hle" as %Hle.
    iApply "HΦ". iExists n. iFrame.
    iSplit; first done.
    iPureIntro. lia.
  Qed.

  Lemma bump_closure_low l :
    mcounter N l 0 ⊢ low (RecV "bump" <> (incr l ;; read l)).
  Proof.
    iIntros "#Hc". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    iApply wp_forget_progress.
    wp_apply (incr_mono_spec N l 0 with "Hc").
    iIntros "Hc1".
    wp_seq.
    wp_apply (read_mono_spec N l 1 with "Hc1").
    iIntros (n) "H".
    iDestruct "H" as "[Hle Hc1]".
    iDestruct "Hle" as %Hle.
    iApply "HΦ". by simpl_low.
  Qed.

  Lemma use_closure_low l :
    mcounter N l 0 ⊢
      low (RecV "use" <>
        (let: "n" := (rec: "bump" <> := incr l ;; read l) () in
         assert: (#0 < "n"))).
  Proof.
    iIntros "#Hc". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    iApply wp_forget_progress.
    wp_apply (bump_cap_call_pos with "Hc").
    iIntros (v) "Hv".
    iDestruct "Hv" as (n) "Hv".
    iDestruct "Hv" as "[Hv Hrest]".
    iDestruct "Hv" as %Hv.
    iDestruct "Hrest" as "[Hpos _]".
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
    wp_apply (newcounter_mono_spec N True%I with "Hh"); first done.
    iIntros (l) "#Hc". wp_let.
    wp_lam. wp_let.
    wp_lam. wp_let.
    wp_let. wp_proj. wp_let.
    wp_lam. wp_let.
    iApply "HΦ". clear Φ. rewrite low_val /=. iNext.
    iSplitL.
    - iPoseProof (use_closure_low l with "Hc") as "Huse".
      by iExact "Huse".
    - iPoseProof (bump_closure_low l with "Hc") as "Hbump".
      by iExact "Hbump".
  Qed.
End proof.

Lemma checked_counter_safe C t2 σ2 :
  AdvCtx C →
  rtc step ([ctx_fill C checked_counter], good_state ∅) (t2, σ2) →
  is_good σ2.
Proof.
  set Σ : gFunctors := #[heapΣ; mcounterΣ].
  set N : namespace := nroot .@ "checked_counter".
  move=>??. eapply (robust_safety Σ); try done.
  { naive_solver eauto using is_closed_of_val. }
  iIntros (?) "Hh". wp_apply (checked_counter_spec N with "Hh"); auto with ndisj.
Qed.

Print Assumptions checked_counter_safe.
