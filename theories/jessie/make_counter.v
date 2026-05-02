From iris.heap_lang Require Import heap adequacy.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From Peg Require Import Match.
From iris.jessie Require Import makeCounter_js.
From iris.jessie Require Import jessie_notation.
From iris.jessie Require Import jessica_ast jessica_to_hla quasi_jessie.
Import uPred.

(** * Upward-capability counter client *)

Definition checkedCounter_source : string :=
  "const checkedCounter = () => {
  const c = makeCounter();
  const cUp = { incr: c.incr };
  const use = () => {
    assert(0 < c.incr());
  };
  return { _fst: use, _snd: cUp };
};".

Module PegMakeCounter.
  Import JessicaAst.

  Definition makeCounter_jessica_fn : jexpr :=
    JArrow []
      (JBodyBlock [
        JLet [JBind (JDef "count") (JDataNum 0)];
        JReturn (JRecord [
          JProp "incr"
            (JArrow [] (JBodyExpr (JAssignOp "+=" (JUse "count") (JDataNum 1))));
          JProp "decr"
            (JArrow [] (JBodyExpr (JAssignOp "-=" (JUse "count") (JDataNum 1))))
        ])
      ]).

  Definition makeCounter_jessica_program : jmodule :=
    JModule [JConst [JBind (JDef "makeCounter") makeCounter_jessica_fn]].

  Example parse_makeCounter_source_program :
    QuasiJessie.parse_program_only makeCounter_source =
      Some makeCounter_jessica_program.
  Proof. vm_compute. reflexivity. Qed.

  (** checkedCounter source parsing *)

  Definition checkedCounter_jessica_fn : jexpr :=
    JArrow []
      (JBodyBlock [
        JConstStmt [JBind (JDef "c") (JCall (JUse "makeCounter") [])];
        JConstStmt [JBind (JDef "cUp") (JRecord [JProp "incr" (JGet (JUse "c") "incr")])];
        JConstStmt [JBind (JDef "use")
          (JArrow [] (JBodyBlock [JAssert (JGreater (JCall (JGet (JUse "c") "incr") []) (JDataNum 0))]))];
        JReturn (JRecord [
          JProp "_fst" (JUse "use");
          JProp "_snd" (JUse "cUp")
        ])
      ]).

  Definition checkedCounter_jessica_program : jmodule :=
    JModule [JConst [JBind (JDef "checkedCounter") checkedCounter_jessica_fn]].

  Example parse_checkedCounter_source_program :
    QuasiJessie.parse_program_only checkedCounter_source =
      Some checkedCounter_jessica_program.
  Proof. vm_compute. reflexivity. Qed.
End PegMakeCounter.

Definition make_counter : val :=
  λ: <>,
    let: "count" := ref #0 in
    jobj [
      "incr" := (λ: "count", λ: <>, "count" += #1) "count";
      "decr" := (λ: "count", λ: <>, "count" -= #1) "count"
    ].

Definition make_counter_expr : expr :=
  λ: <>,
    let: "count" := ref #0 in
    jobj [
      "incr" := (λ: "count", λ: <>, "count" += #1) "count";
      "decr" := (λ: "count", λ: <>, "count" -= #1) "count"
    ].

Lemma make_counter_expr_of_val :
  of_val make_counter = make_counter_expr.
Proof. solve_of_val_unlock. Qed.

Lemma jessica_to_hla_makeCounter_fn :
  JessicaToHla.jessica_expr_to_hla [] PegMakeCounter.makeCounter_jessica_fn =
    Some make_counter_expr.
Proof. vm_compute. reflexivity. Qed.

Lemma jessica_to_hla_makeCounter_is_make_counter_binding :
  JessicaToHla.jessica_to_hla_module PegMakeCounter.makeCounter_jessica_program =
    Some (let: "makeCounter" := make_counter_expr in ())%E.
Proof. vm_compute. reflexivity. Qed.

Definition checkedCounter_lowered_expr : expr :=
  λ: <>,
    let: "c" := "makeCounter" () in
    let: "cUp" := jobj ["incr" := "c" @[ "incr" ]] in
    let: "use" := (λ: "cUp",
      (λ: "c",
        λ: <>, assert: (#0 < "c" @[ "incr" ] ());; ()) "c") "cUp" in
    jobj ["_fst" := "use"; "_snd" := "cUp"].

Lemma jessica_to_hla_checkedCounter_fn :
  JessicaToHla.jessica_expr_to_hla [] PegMakeCounter.checkedCounter_jessica_fn =
    Some checkedCounter_lowered_expr.
Proof. vm_compute. reflexivity. Qed.

Lemma jessica_to_hla_checkedCounter_program :
  JessicaToHla.jessica_to_hla_module PegMakeCounter.checkedCounter_jessica_program =
    Some (let: "checkedCounter" := checkedCounter_lowered_expr in ())%E.
Proof. vm_compute. reflexivity. Qed.

Definition checked_counter : expr :=
  let: "c" := make_counter () in
  let: "cUp" := jobj ["incr" := "c" @[ "incr" ]] in
  let: "use" := (λ: "cUp",
    λ: <>,
      let: "cUpIncr" := "cUp" @[ "incr" ] in
      let: "n" := "cUpIncr" () in
      assert: (#0 < "n")) "cUp" in
  ("use", "cUp").

Definition counter_val (count : loc) : val :=
  j_objectV2 "incr" (LamV <> (count += #1))
             "decr" (LamV <> (count -= #1)).

Definition c_up_val (count : loc) : val :=
  (#object_tag, ((incr_key, LamV <> (count += #1)), ()))%V.

Section proof.
  Context `{heapG Σ}.
  Context (N : namespace) (HN : heapN ⊥ N).

  Definition counter_inv (count : loc) : iProp Σ :=
    (inv N (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z))%I.

  Lemma wp_obj_get1 k v :
    {{{ True }}}
      (jobj [k := (of_val v)]) @[ k ]
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "HΦ". rewrite /obj_get /obj_get_fields.
    wp_lam. wp_lam.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_apply wp_assert. wp_op=>?; last done.
    iSplit; first done.
    iNext. wp_finish. wp_rec. wp_let.
    wp_op=>[EQ|NEQ].
    - exfalso. by discriminate EQ.
    - etrans; [|eapply wp_if_false]. wp_finish.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_proj.
    wp_op=>[EQ'|NEQ']; [etrans; [|eapply wp_if_true]; wp_finish|exfalso; apply NEQ'; reflexivity].
    wp_proj. by iApply "HΦ".
  Qed.

  Lemma wp_obj_get2_first k1 k2 v1 v2 :
    {{{ True }}}
      (jobj [k1 := (of_val v1); k2 := (of_val v2)]) @[ k1 ]
    {{{ RET v1; True }}}.
  Proof.
    iIntros (Φ) "HΦ". rewrite /obj_get /obj_get_fields.
    wp_lam. wp_lam.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_apply wp_assert. wp_op=>?; last done.
    iSplit; first done.
    iNext. wp_finish. wp_rec. wp_let.
    wp_op=>[EQ|NEQ].
    - exfalso. by discriminate EQ.
    - etrans; [|eapply wp_if_false]. wp_finish.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_proj.
    wp_op=>[EQ'|NEQ']; [etrans; [|eapply wp_if_true]; wp_finish|exfalso; apply NEQ'; reflexivity].
    wp_proj. by iApply "HΦ".
  Qed.

  Lemma wp_counter_get_incr (count : loc) :
    {{{ True }}}
      (counter_val count) @[ "incr" ]
    {{{ RET (LamV <> (count += #1)); True }}}.
  Proof.
    rewrite /counter_val /incr_key.
    apply (wp_obj_get2_first "incr" "decr").
  Qed.

  Lemma wp_c_up_get_incr (count : loc) :
    {{{ True }}}
      (c_up_val count) @[ "incr" ]
    {{{ RET (LamV <> (count += #1)); True }}}.
  Proof.
    rewrite /c_up_val.
    iIntros (Φ) "HΦ". rewrite /obj_get /obj_get_fields.
    wp_lam. wp_lam.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_apply wp_assert. wp_op=>?; last done.
    iSplit; first done.
    iNext. wp_finish. wp_rec. wp_let.
    wp_op=>[EQ|NEQ].
    - exfalso. by discriminate EQ.
    - etrans; [|eapply wp_if_false]. wp_finish.
    wp_proj. wp_let.
    wp_proj. wp_let.
    wp_proj.
    wp_op=>[EQ'|NEQ']; [etrans; [|eapply wp_if_true]; wp_finish|exfalso; apply NEQ'; reflexivity].
    wp_proj. by iApply "HΦ".
  Qed.

  Lemma make_counter_spec :
    {{{ heap_ctx }}}
      make_counter ()
    {{{ count, RET (counter_val count); counter_inv count }}}.
  Proof.
    iIntros (Φ) "#Hh HΦ". rewrite /make_counter /counter_val.
    wp_lam.
    wp_alloc count as "Hcount". wp_let.
    iMod (inv_alloc N _ (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z)%I with "[Hcount]") as "#Hinv".
    { iNext. iExists 0. iFrame. done. }
    wp_bind ((λ: "count", λ: <>, "count" += #1) count)%E.
    wp_lam.
    wp_bind ((λ: "count", λ: <>, "count" -= #1) count)%E.
    wp_lam.
    by iApply ("HΦ" $! count with "Hinv").
  Qed.

  Lemma incr_call_pos count :
    {{{ heap_ctx ∗ counter_inv count }}}
      (LamV <> (count += #1)) ()
    {{{ v, RET v; ∃ z : Z, ⌜v = #z⌝ ∗ ⌜0 < z⌝ }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hinv) HΦ".
    wp_lam.
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
      low (LamV <> (count += #1)).
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

  Lemma c_up_low count :
    heap_ctx ∗ counter_inv count ⊢ low (c_up_val count).
  Proof.
    iIntros "#H". rewrite /c_up_val /incr_key /j_string.
    simpl_low. iNext. iSplit; first done.
    iNext. iSplit; last done.
    iNext. iSplit.
    - iNext. iSplit; done.
    - by iApply (incr_closure_low with "H").
  Qed.

  Lemma use_closure_low count :
    heap_ctx ∗ counter_inv count ⊢
      low (LamV <>
        (let: "cUpIncr" := (c_up_val count) @[ "incr" ] in
         let: "n" := "cUpIncr" () in
         assert: (#0 < "n"))).
  Proof.
    iIntros "#(Hh & Hinv)". rewrite low_rec.
    iAlways. iNext. iIntros (? Φ) "_ HΦ". simpl_subst.
    wp_apply (wp_forget_progress progress).
    wp_apply (wp_c_up_get_incr count).
    iIntros "_".
    wp_let.
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
    iIntros (Φ) "#Hh HΦ". rewrite /checked_counter.
    wp_apply (make_counter_spec with "Hh").
    iIntros (count) "#Hinv".
    wp_let.
    wp_apply (wp_counter_get_incr count).
    iIntros "_".
    wp_let.
    wp_let.
    wp_let.
    iApply "HΦ".
    clear Φ.
    rewrite low_val /=. iNext.
    iSplitL.
    - rewrite low_rec.
      iAlways. iNext. iIntros (? Ψ) "_ HΨ". simpl_subst.
      wp_apply (wp_forget_progress progress).
      wp_apply (wp_c_up_get_incr count).
      iIntros "_".
      wp_let.
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
      by iApply "HΨ"; simpl_low.
    - by iApply (c_up_low with "[$Hh $Hinv]").
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
