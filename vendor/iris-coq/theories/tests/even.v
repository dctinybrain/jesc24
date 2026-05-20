From iris.heap_lang Require Import heap.
From iris.heap_lang.lib Require Import assume.
From iris.heap_lang Require Import proofmode notation.

(** * Reference monitors accepting even integers *)

Definition assert_even : val := λ: "n", assert: even: "n" ;; "n".
Definition assume_even : val := λ: "n", assume: even: "n" ;; "n".

Section monitors.
  Context `{heapG Σ}.
  Implicit Types n : Z.
  Implicit Types v : val.

  Definition is_even (v : val) : iProp Σ :=
    (∃ n : Z, ⌜v = #n⌝ ∗ ⌜Z.Even n⌝)%I.

  Global Instance is_even_persistent v : PersistentP (is_even v).
  Proof. apply _. Qed.

  Lemma is_even_low v : is_even v ⊢ low v.
  Proof.
    iIntros "Hv". iDestruct "Hv" as (n) "[EQ _]". iDestruct "EQ" as %->.
    by simpl_low.
  Qed.

  Lemma assert_even_spec v :
    {{{ is_even v }}} assert_even v {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "Hv HΦ". wp_lam.
    wp_apply wp_assert.
    iDestruct "Hv" as (n) "(EQ & EV)".
      iDestruct "EQ" as %[=->]. iDestruct "EV" as "%".
    wp_op=>?.
    - iSplit; first done. iNext. wp_seq. by iApply "HΦ".
    - iExFalso. iPureIntro. exact: Z.Even_Odd_False.
  Qed.

  Lemma assume_even_spec v :
    {{{ True }}} assume_even v ?{{{ RET v; is_even v }}}.
  Proof.
    iIntros (Φ) "HΦ". wp_lam.
    wp_apply wp_assume.
    case: (decide (is_int (of_val v)))=>Hint;
      last by wp_apply wp_stuck_even.
      destruct (is_int_val _ Hint) as (n&->).
    wp_op=>?.
    - iIntros "_ !>". wp_seq. rewrite/is_even. by iApply "HΦ"; auto.
    - iIntros "%". by iExFalso.
  Qed.
End monitors.
