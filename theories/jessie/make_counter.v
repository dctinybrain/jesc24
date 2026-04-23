From iris.heap_lang Require Import heap adequacy.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.jessie.peg Require Import peg_match.
From iris.jessie Require Import makeCounter_js.
From iris.jessie Require Import jessie_notation jessie_parse.
From iris.jessie Require Import jessica_ast quasi_jessie.
Import uPred.

(** * Upward-capability counter client *)

Definition checkedCounter_source : string :=
  "const c = makeCounter();
const cUp = { incr: c.incr };
attacker(cUp);
assert(c.incr() > 0);".

Module PegMakeCounter.
  Module JA := JessicaAst.

  Definition count_use : JA.jexpr := JA.JUse "count".
  Definition data0 : JA.jexpr := JA.JDataNum 0.
  Definition data1 : JA.jexpr := JA.JDataNum 1.

  Definition incr_prop : JA.jprop :=
    JA.JProp "incr"
      (JA.JArrow [] (JA.JBodyExpr (JA.JAssignOp "+=" count_use data1))).

  Definition decr_prop : JA.jprop :=
    JA.JProp "decr"
      (JA.JArrow [] (JA.JBodyExpr (JA.JAssignOp "-=" count_use data1))).

  Definition count_let : JA.jstmt :=
    JA.JLet [JA.JBind (JA.JDef "count") data0].

  Definition counter_record : JA.jexpr :=
    JA.JRecord [incr_prop; decr_prop].

  Definition makeCounter_jessica_program : JA.jmodule :=
    JA.JModule
      [JA.JConst
        [JA.JBind
          (JA.JDef "makeCounter")
          (JA.JArrow [] (JA.JBodyBlock [count_let; JA.JReturn counter_record]))]].

  Example parse_makeCounter_module :
    matches_comp QuasiJessie.grammar QuasiJessie.moduleBody
      makeCounter_source 4096 = Some (Success EmptyString).
  Proof. vm_compute. reflexivity. Qed.

  Example parse_makeCounter_source_program :
    QuasiJessie.parse_program_only makeCounter_source =
      Some makeCounter_jessica_program.
  Proof. vm_compute. reflexivity. Qed.
End PegMakeCounter.

Definition makeCounter_program : list jstmt :=
  [SConst "makeCounter"
    (EArrow [] (JArrowBlock
      [SLet "count" (ENum 0);
       SReturn
         (EObject
           [("incr", EArrow [] (JArrowExpr (EOpAssign PlusOp "count" 1)));
            ("decr", EArrow [] (JArrowExpr (EOpAssign MinusOp "count" 1)))])]))].

Definition make_counter : val :=
  λ: <>,
    let: "count" := ref #0 in
    jobj [
      "incr" := (λ: "count", rec: "f" <> := "count" += #1) "count";
      "decr" := (λ: "count", rec: "f" <> := "count" -= #1) "count"
    ].

Definition makeCounter_program_term : expr :=
  compile_program_expr makeCounter_program.

Example parse_makeCounter_source_program :
  parse_program_only makeCounter_source = Some makeCounter_program.
Proof. vm_compute. reflexivity. Qed.

Lemma compile_makeCounter_program_expr :
  compile_program_expr makeCounter_program = makeCounter_program_term.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma parse_makeCounter_source_program_term :
  compile_parsed_program_expr makeCounter_source = Some makeCounter_program_term.
Proof.
  rewrite /compile_parsed_program_expr parse_makeCounter_source_program.
  rewrite compile_makeCounter_program_expr.
  reflexivity.
Qed.

Definition checkedCounter_program : list jstmt :=
  [SConst "c" (ECall (EVar "makeCounter") []);
   SConst "cUp" (EObject [("incr", EGet (EVar "c") "incr")]);
   SExpr (ECall (EVar "attacker") [EVar "cUp"]);
   SAssert (EGreater (ECall (EGet (EVar "c") "incr") []) (ENum 0))].

Definition checkedCounter_program_term : expr :=
  compile_program_expr checkedCounter_program.

Example parse_checkedCounter_source_program :
  parse_program_only checkedCounter_source = Some checkedCounter_program.
Proof. vm_compute. reflexivity. Qed.

Lemma compile_checkedCounter_program_expr :
  compile_program_expr checkedCounter_program = checkedCounter_program_term.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_checkedCounter_source_program_term :
  compile_parsed_program_expr checkedCounter_source = Some checkedCounter_program_term.
Proof.
  rewrite /compile_parsed_program_expr parse_checkedCounter_source_program.
  rewrite compile_checkedCounter_program_expr.
  reflexivity.
Qed.

Definition checked_counter : expr :=
  let: "c" := make_counter () in
  let: "cUpIncr" := obj_get "c" incr_key in
  let: "use" := (λ: "cUpIncr",
    rec: "use" <> :=
      let: "n" := "cUpIncr" () in
      assert: (#0 < "n")) "cUpIncr" in
  (* TODO: change this back to the object-shaped cUp export once the proof
     goes through cleanly with object lookup in both places. *)
  ("use", "cUpIncr").

(* TODO: Relate the parsed [checkedCounter_program_term], which keeps the
   object-shaped [cUp] and an external [attacker], to the narrower
   proof-oriented [checked_counter] term below. *)

Definition counter_val (count : loc) : val :=
  j_objectV2 "incr" (RecV "f" <> (count += #1))
             "decr" (RecV "f" <> (count -= #1)).

Section proof.
  Context `{heapG Σ}.
  Context (N : namespace) (HN : heapN ⊥ N).

  Definition counter_inv (count : loc) : iProp Σ :=
    (inv N (∃ z : Z, ⌜0 ≤ z⌝ ∗ count ↦ #z))%I.

  Lemma wp_obj_get2_first k1 k2 v1 v2 :
    {{{ True }}}
      obj_get (jobj [k1 := (of_val v1); k2 := (of_val v2)]) (j_string k1)
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
      obj_get (counter_val count) incr_key
    {{{ RET (RecV "f" <> (count += #1)); True }}}.
  Proof.
    rewrite /counter_val /incr_key.
    apply (wp_obj_get2_first "incr" "decr").
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
    wp_bind ((λ: "count", rec: "f" <> := "count" += #1) count)%E.
    wp_lam.
    wp_bind ((λ: "count", rec: "f" <> := "count" -= #1) count)%E.
    wp_lam.
    by iApply ("HΦ" $! count with "Hinv").
  Qed.

  Lemma incr_call_pos count :
    {{{ heap_ctx ∗ counter_inv count }}}
      (RecV "f" <> (count += #1)) ()
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
      low (RecV "f" <> (count += #1)).
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
        (let: "n" := (rec: "f" <> := count += #1) () in
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
