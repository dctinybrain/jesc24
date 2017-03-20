From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import sealing assume.
From iris.heap_lang.lib Require lock spin_lock.
From iris.heap_lang Require Import notation proofmode.
Import sealing.intf.

Section lifting.	(* PDS: Hoist. *)
  Context `{ownPG heap_lang Σ}.
  Local Hint Resolve to_of_val.
  Implicit Types n : Z.
  Implicit Types v : val.

  Lemma wp_stuck_lt_l E v1 v2 Φ :
    ¬ is_int (of_val v1) → WP v1 ≤ v2 @ E ?{{ Φ }}%I.
  Proof.
    move=>Hv1. iApply wp_stuck_bin_op=>//.
    case: v1 Hv1 => //. case=>//. rewrite/is_int. by naive_solver.
  Qed.

  Lemma wp_stuck_lt_r E n1 v2 Φ :
    ¬ is_int (of_val v2) → WP #n1 ≤ v2 @ E ?{{ Φ }}%I.
  Proof.
    move=>Hv2. iApply wp_stuck_bin_op=>//.
    case: v2 Hv2 => //. case=>//. rewrite/is_int. by naive_solver.
  Qed.
End lifting.

(** * Protected interval manipulating routines *)
(**
	Other than the assertion on unsealing, this is a
	transliteration of Morris' example.
*)
Section intervals_code.
  Context {SI : SealingImpl}.

  Definition intervals : expr :=
    let: "p" := make_seal () in
    let: "seal" := Fst "p" in let: "unseal" := Snd "p" in
    let: "unseal" := λ: "x",
      let: "i" := "unseal" "x" in assert: (Fst "i" ≤ Snd "i") ;; "i"
    in
    let: "make_int" := λ: "n1" "n2",
      "seal" (if: "n1" ≤ "n2" then ("n1", "n2") else ("n2", "n1"))
    in
    let: "min" := λ: "x", Fst ("unseal" "x") in
    let: "max" := λ: "x", Snd ("unseal" "x") in
    let: "sum" := λ: "x" "y",
      let: "i" := "unseal" "x" in
      let: "j" := "unseal" "y" in
      "seal" (Fst "i" + Fst "j", Snd "i" + Snd "j")
    in ("make_int", "min", "max", "sum").
End intervals_code.

Section intervals_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.

  Definition is_int' (n1 n2 : Z) (v : val) : iProp Σ :=
    (⌜v = (#n1, #n2)%V⌝ ∗ ⌜n1 ≤ n2⌝)%I.

  Instance is_int'_persistent n1 n2 v :
    PersistentP (is_int' n1 n2 v).
  Proof. apply _. Qed.

  Notation intφ := (λ v, (∃ n1 n2, is_int' n1 n2 v))%I (only parsing).
  Instance intφ_persistent v : PersistentP (intφ v).
  Proof. apply _. Qed.

  Record ctx : Type := { γ : name S; seal : val; unseal : val }.

  Definition int_ctx (ctx : ctx) : iProp Σ := (
    is_sealing S (γ ctx) intφ ∗
    is_seal S (γ ctx) (seal ctx) ∗
    is_unseal S (γ ctx) (unseal ctx)
  )%I.

  Definition is_interval (ctx : ctx) (n1 n2 : Z) (v : val) : iProp Σ :=
    (is_sealed S (γ ctx) (#n1, #n2)%V v)%I.

  (** The make interval function. *)

  Definition is_make_int (ctx : ctx) (v : val) : iProp Σ := (
    ⌜v = LamV "n1" (λ: "n2",
      (seal ctx) (if: "n1" ≤ "n2" then ("n1", "n2") else ("n2", "n1")))⌝
  )%I.
  Definition is_make_int_2 (ctx : ctx) (n1 : Z) (v : val) : iProp Σ := (
    ⌜v = LamV "n2" (
      (seal ctx) (if: #n1 ≤ "n2" then (#n1, "n2") else ("n2", #n1)))%E⌝
  )%I.
  Definition make_int_body ctx (e1 e2 : expr) : expr :=
    ((seal ctx) (if: e1 ≤ e2 then (e1, e2) else (e2, e1)))%E.
  Notation MkInt ctx v n1 n2 := (
    low v%V ∗ is_interval ctx (Z.min n1 n2) (Z.max n1 n2) v
  )%I (only parsing).

  Lemma make_int_body_nn p ctx n1 n2 :
    {{{ int_ctx ctx }}} make_int_body ctx (#n1) (#n2) @ p; ⊤
    {{{ v, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "#(HS&Hs&Hu) HΦ".
      rewrite/make_int_body/is_interval/is_int'.
    wp_op=>[?|/Z.lt_le_incl ?]; wp_if; wp_apply (seal_spec with "[$HS $Hs]").
    - by iExists n1, n2; auto. by rewrite (Z.min_l n1) // (Z.max_r _ n2).
    - by iExists n2, n1; auto. by rewrite (Z.min_r _ n2) // (Z.max_l n1).
  Qed.

  Lemma make_int_body_nv ctx n1 v2 :
    {{{ int_ctx ctx }}} make_int_body ctx (#n1) v2
    ?{{{ v n2, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "Hctx HΦ". rewrite/make_int_body.
    case: (decide (is_int (of_val v2)))=>Hv2; last by wp_apply wp_stuck_lt_r.
      destruct (is_int_val _ Hv2) as (n2&->).
    wp_apply (make_int_body_nn with "Hctx"). iIntros (v) "Hv".
    by iApply ("HΦ" $! _ n2 with "Hv").
  Qed.

  Lemma make_int_body_vv ctx v1 v2 :
    {{{ int_ctx ctx }}} make_int_body ctx v1 v2
    ?{{{ v n1 n2, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "Hctx HΦ". rewrite/make_int_body.
    case: (decide (is_int (of_val v1)))=>Hv1; last by wp_apply wp_stuck_lt_l.
      destruct (is_int_val _ Hv1) as (n1&->).
    wp_apply (make_int_body_nv with "Hctx"). iIntros (v n2) "Hv".
    by iApply ("HΦ" $! _ n1 with "Hv").
  Qed.

  Lemma make_int_2_spec p ctx mk n1 n2 :
    {{{ int_ctx ctx ∗ is_make_int_2 ctx n1 mk }}} mk #n2 @ p; ⊤
    {{{ v, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by wp_apply (make_int_body_nn with "Hctx [$HΦ]").
  Qed.

  (* PDS: Annoying without [make_int_any_spec]. *)
  Lemma make_int_2_any_spec ctx mk n1 v2 :
    {{{ int_ctx ctx ∗ is_make_int_2 ctx n1 mk }}} mk v2
    ?{{{ v n2, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by wp_apply (make_int_body_nv with "Hctx [$HΦ]").
  Qed.

  Lemma make_int_2_low_spec ctx mk n1 :
    int_ctx ctx -∗ is_make_int_2 ctx n1 mk -∗ low mk.
  Proof.
    iIntros "#Hctx %". subst. rewrite low_rec. iAlways. iNext.
    iIntros (v2 Φ) "_ HΦ". simpl_subst.
    wp_apply (make_int_body_nv with "Hctx"). iIntros (v ?) "[Hv _]".
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma make_int_spec p ctx mk n1 :
    {{{ int_ctx ctx ∗ is_make_int ctx mk }}} mk #n1 @ p; ⊤
    {{{ f, RET f; is_make_int_2 ctx n1 f }}}.
  Proof. iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam. by iApply "HΦ". Qed.

  Lemma make_int_any_spec p ctx mk v1 :
    {{{ int_ctx ctx ∗ is_make_int ctx mk }}} mk v1 @ p; ⊤
    {{{ f n1, RET f; is_make_int_2 ctx n1 f }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam. (* no progress *)
  Abort.

  Lemma make_int_low_spec ctx mk :
    int_ctx ctx -∗ is_make_int ctx mk -∗ low mk.
  Proof.
    iIntros "#Hctx %". subst. rewrite low_rec. iAlways. iNext.
    iIntros (v1 Φ) "_ HΦ". simpl_subst. wp_value.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
    iIntros (v2 Φ) "_ HΦ". simpl_subst.
    wp_apply (make_int_body_vv with "Hctx"). iIntros (v ??) "[Hv _]".
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma make_int_val_spec p ctx mk n1 n2 :
  {{{ int_ctx ctx ∗ is_make_int ctx mk }}} mk #n1 #n2 @ p; ⊤
  {{{ v, RET v; MkInt ctx v n1 n2 }}}.
  Proof.
    iIntros (Φ) "[#Hctx Hmk] HΦ".
    wp_apply (make_int_spec with "[$Hctx $Hmk]"). iIntros (f) "Hf".
    by wp_apply (make_int_2_spec with "[$Hctx $Hf] [$HΦ]").
  Qed.

  (** The unseal function. *)

  Lemma unseal_spec p γ s :
    {{{ is_interval_sealer γ s }}} unseal' SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
   wp_apply (unseal_sealed_val with "[$Hs $Hv']").
      iDestruct 1 as (n'1 n'2) "[EQ %]". iDestruct "EQ" as %[=<-<-]. wp_let.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "[%]").
  Qed.

  (** The min function. *)

  Definition is_min (ctx : ctx) (v : val) : iProp Σ := (
    ⌜v = LamV "x" (Fst ((unseal ctx) "x"))⌝
  )%I.

  Definition is_max (ctx : ctx) (v : val) : iProp Σ := (
    ⌜v = LamV "x" (Snd ((unseal ctx) "x"))⌝
  )%I.

  Definition is_sum (ctx : ctx) (v : val) : iProp Σ := (
    ⌜v = LamV "x" (λ: "y",
      let: "i" := (unseal ctx) "x" in
      let: "j" := (unseal ctx) "y" in
      (seal ctx) (Fst "i" + Fst "j", Snd "i" + Snd "j"))⌝
  )%I.

  Definition is_sum_2 (ctx : ctx) (x : val) (v : val) : iProp Σ := (
    ⌜v = LamV "y" (
      let: "i" := (unseal ctx) x in
      let: "j" := (unseal ctx) "y" in
      (seal ctx) (Fst "i" + Fst "j", Snd "i" + Snd "j"))⌝
  )%I.






  Lemma unseal'_spec p γ s :
    {{{ is_interval_sealer γ s }}} unseal' SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
   wp_apply (unseal_sealed_val with "[$Hs $Hv']").
      iDestruct 1 as (n'1 n'2) "[EQ %]". iDestruct "EQ" as %[=<-<-]. wp_let.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "[%]").
  Qed.

  Lemma unseal'_val_spec p γ s n1 n2 v' :
    {{{ is_interval_sealer γ s ∗ is_interval γ n1 n2 v' }}}
      unseal' SI s v' @ p; ⊤
    {{{ RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ".
    wp_apply (unseal'_spec with "Hs"). iIntros (f) "Hf".
    by wp_apply ("Hf" with "* Hv' [$HΦ]").
  Qed.

  Lemma unseal'_low_spec γ s v' :
    {{{ is_interval_sealer γ s ∗ low v' }}} unseal' SI s v'
    ?{{{ n1 n2, RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ". do 2!wp_lam.
    wp_apply (unseal_low_val with "[$Hs $Hv']"). iIntros (v) "#Hv". wp_let.
      iDestruct "Hv" as (n1 n2) "Hv".
      iDestruct (persistentP with "Hv") as ">[%%]". subst.
      do 2!wp_proj. wp_op=>?; last by exfalso; lia.
    wp_apply wp_assert. iSplit; first done. iNext. wp_seq.
    by iApply ("HΦ" with "[%]").
  Qed.

  Lemma min_spec p γ s :
    {{{ is_interval_sealer γ s }}} min SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET #n1; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
    wp_apply (unseal'_val_spec with "[$Hs $Hv']"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} min SI s @ p; ⊤ {{{ f, RET f;
      low f ∗ ∀ v', {{{ low v' }}} f v' ?{{{ n1, RET #n1; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    - rewrite low_rec. iAlways. iNext. iIntros (v' Φ) "Hv' HΦ". simpl_subst.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      iApply "HΦ". by simpl_low.
    - iIntros (v') "!#". iIntros (Φ) "Hv' HΦ". wp_lam.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      by iApply "HΦ".
  Qed.

  Lemma max_spec p γ s :
    {{{ is_interval_sealer γ s }}} max SI s @ p; ⊤ {{{ f, RET f; ∀ p n1 n2 v',
      {{{ is_interval γ n1 n2 v' }}} f v' @ p; ⊤ {{{ RET #n2; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v') "!#". iIntros (Φ) "Hv' HΦ".
      wp_lam.
    wp_apply (unseal'_val_spec with "[$Hs $Hv']"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma max_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} max SI s @ p; ⊤ {{{ f, RET f;
      low f ∗ ∀ v', {{{ low v' }}} f v' ?{{{ n2, RET #n2; True }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    - rewrite low_rec. iAlways. iNext. iIntros (v' Φ) "Hv' HΦ". simpl_subst.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      iApply "HΦ". by simpl_low.
    - iIntros (v') "!#". iIntros (Φ) "Hv' HΦ". wp_lam.
      wp_apply (unseal'_low_spec with "[$Hs $Hv']"). iIntros (n1 n2) "%".
        wp_proj.
      by iApply "HΦ".
  Qed.

  Lemma sum_spec p γ s :
    {{{ is_interval_sealer γ s }}} sum SI s @ p; ⊤ {{{ f1, RET f1;
      ∀ p n1 n2 v1, {{{ is_interval γ n1 n2 v1 }}} f1 v1 @ p; ⊤ {{{ f2, RET f2;
        ∀ p n'1 n'2 v2, {{{ is_interval γ n'1 n'2 v2 }}} f2 v2 @ p; ⊤ {{{
          v', RET v'; low v' ∗ is_interval γ (n1+n'1) (n2+n'2) v'
        }}}
      }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n1 n2 v1) "!#". iIntros (Φ) "#Hv1 HΦ".
      wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p n'1 n'2 v2) "!#". iIntros (Φ) "Hv2 HΦ".
      wp_lam.
    wp_apply (unseal'_val_spec with "[$Hs $Hv1]"). iIntros "%". wp_let.
    wp_apply (unseal'_val_spec with "[$Hs $Hv2]"). iIntros "%". wp_let.
    wp_apply (seal_spec with "Hs"). iIntros (f) "[_ Hf]".
      do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
    wp_apply ("Hf" with "* [] [$HΦ]"). iExists _, _. iSplitL; first done.
    iPureIntro. by lia.
  Qed.

  Lemma sum_low_spec p γ s :
    {{{ is_interval_sealer γ s }}} sum SI s @ p; ⊤ {{{ f1, RET f1;
      low f1 ∗ ∀ v1, {{{ low v1 }}} f1 v1 ?{{{ f2, RET f2;
        low f2 ∗ ∀ v2, {{{ low v2 }}} f2 v2 ?{{{ n1 n2 v, RET v;
          is_interval γ n1 n2 v
        }}}
      }}}
    }}}.
  Proof.
    assert (Hbody :
      ∀ v1 v2,
      {{{ is_interval_sealer γ s ∗ low v1 ∗ low v2 }}}
        let: "i" := unseal' SI s v1 in let: "j" := unseal' SI s v2 in
        seal SI s (Fst "i" + Fst "j", Snd "i" + Snd "j")
      ?{{{ n1 n2 v, RET v; low v ∗ is_interval γ n1 n2 v }}}
    ).
    { iIntros (v1 v2 Φ) "#(Hs & Hv1 & Hv2) HΦ".
      wp_apply (unseal'_low_spec with "[$Hs $Hv1]").
        iIntros (n1 n2) "%". wp_let.
      wp_apply (unseal'_low_spec with "[$Hs $Hv2]").
        iIntros (n'1 n'2) "%". wp_let.
      wp_apply (seal_spec with "Hs"). iIntros (f) "[_ Hf]".
        do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
      wp_apply ("Hf" with "* [] [HΦ]").
      + iExists _, _. iSplit; first done. iPureIntro. by lia.
      + iIntros (?) "?". iApply "HΦ". by iFrame. }
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iSplitL.
    { rewrite low_rec. iAlways. iNext. iIntros (v1 Φ) "#Hv1 HΦ".
        simpl_subst. wp_value.
      iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
        iIntros (v2 Φ) "#Hv2 HΦ". simpl_subst.
      wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[? _]".
      by iApply "HΦ". }
    iIntros (v1) "!#". iIntros (Φ) "#Hv1 HΦ". wp_lam.
    iApply "HΦ". clear Φ. iSplitL.
    { rewrite low_rec. iAlways. iNext. iIntros (v2 Φ) "#Hv2 HΦ".
        simpl_subst.
      wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[? _]".
      by iApply "HΦ". }
    iIntros (v2) "!#". iIntros (Φ) "#Hv2 HΦ". wp_lam.
    wp_apply (Hbody with "* [$Hs $Hv1 $Hv2]"). iIntros (???) "[_ ?]".
    by iApply "HΦ".
  Qed.

  Lemma use_spec p γ s :
    {{{ is_interval_sealer γ s }}} use SI s @ p; ⊤ {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v Φ) "_ HΦ". simpl_subst.
    wp_apply (unseal'_spec with "Hs"). iIntros (k) "Hk".
    wp_apply (make_interval_spec with "Hs"). iIntros (k1) "Hk1".
    wp_apply ("Hk1" with "* []"); first done. iIntros (k2) "Hk2".
    wp_apply ("Hk2" with "* []"); first done. iIntros (v') "[_ Hv']".
    wp_apply ("Hk" with "* Hv'"). iIntros "%". wp_let.
      rewrite (Z.min_l 0) // (Z.max_r _ 10) //.
    wp_apply wp_assert. wp_proj. wp_op=>Hlo; last by case: Hlo.
      iSplit; first done. iNext. wp_seq.
    wp_apply wp_assert. wp_proj. wp_op=>Hhi; last by case: Hhi.
      iSplit; first done. iNext.
    iApply "HΦ". by simpl_low.
  Qed.

  Lemma intervals_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} intervals SI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/intervals.
    set φ : val → iProp Σ := λ v, (∃ n1 n2, is_interval' n1 n2 v)%I.
    wp_apply (make_sealer_unsealer_spec S N _ φ with "Hh");
      first done. iIntros (s γ) "#Hs". wp_let.
    wp_apply (use_spec with "Hs"). iIntros (use) "Huse".
    wp_apply (make_interval_low_spec with "Hs"). iIntros (mk) "Hmk".
    wp_apply (min_low_spec with "Hs"). iIntros (min) "[Hmin _]".
    wp_apply (max_low_spec with "Hs"). iIntros (max) "[Hmax _]".
    wp_apply (sum_low_spec with "Hs"). iIntros (sum) "[Hsum _]".
      wp_value.
    iApply "HΦ". simpl_low. by iFrame "Huse Hmk Hmin Hmax Hsum".
  Qed.
End intervals_proof.

Section intervals_client_code.
  Context {SI : SealingImpl}.

  Definition interval_client : expr :=
    let: "p" := intervals in
    let: "make_int" := Fst $ Fst $ Fst "p" in
    let: "min" := Snd $ Fst $ Fst "p" in
    let: "max" := Snd $ Fst "p" in
    let: "sum" := Snd "p" in
    let: "i100" := "sum" ("make_int" #1 #0) ("make_int" #(-1) #100) in
    let: <> := assert: "min" "i0" = #0 in
    let: "use" := λ: "i",
      assert: ("min" "i" ≤ "max" "i") ;;
      "sum" "i" "i100"
    in
    ("use", "p").
End intervals_client_code.

(** * Public-key interfaces for sealer-unsealer pairs *)
(**
	When instantiated with suitable representation invariants,
	sealer-unsealer pairs satisfy natural interfaces for
	asymmetric signature and encryption schemes.
*)
Section pk_code.
  Context {SI : SealingImpl}.

  Definition make_key_pair : val := λ: <>,
    let: "k" := make_sealer_unsealer SI () in
    (seal SI "k", unseal SI "k").
End pk_code.

Section pk_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.

  Section sig_triples.
    Context (φ : val → iProp Σ) (sig : val → val → iProp Σ).
    Definition is_sign (sign : val) : iProp Σ := (∀ p v,
      {{{ φ v }}} sign v @ p; ⊤ {{{ v', RET v'; low v' ∗ □ sig v v' }}}
    )%I.
    Definition verify_sig (verify : val) : iProp Σ :=
      (∀ v v', {{{ sig v v' }}} verify v' {{{ RET v; φ v }}})%I.
    Definition verify_low (verify : val) : iProp Σ :=
      (∀ v', {{{ low v' }}} verify v' ?{{{ v, RET v; φ v }}})%I.
    Definition is_verify (v : val) : iProp Σ :=
      (low v ∗ verify_sig v ∗ verify_low v)%I.
  End sig_triples.

  Lemma signature_scheme_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx ∗ to_low φ }}} make_key_pair () @ p; ⊤
    {{{ v1 v2 sig, RET (v1, v2); is_sign φ sig v1 ∗ is_verify φ sig v2 }}}.
  Proof.
    iIntros (? Φ) "#[Hh Hφ] HΦ". wp_lam.
    wp_apply (make_sealer_unsealer_spec S N _ φ with "Hh");
      first done. iIntros (k γ) "#Hk". wp_let.
    wp_apply (seal_spec with "Hk"). iIntros (sign) "[_ #Hsign]".
    wp_apply (unseal_low_spec with "Hk").
      iIntros (verify) "[Hvlow #Hverify]". wp_value.
    iApply ("HΦ" $! _ _ (is_sealed S N γ)). clear p Φ. iSplitR.
    { iIntros (p v) "!#". iIntros (Φ) "Hv HΦ".
      wp_apply ("Hsign" with "* Hv"). iIntros (v') "[Hv'l #Hv's]".
      iApply ("HΦ" with "[$Hv'l Hv's]"). by iAlways. }
    iSplitL.
    { by iApply ("Hvlow" with "Hφ"). }
    iFrame "Hverify".
    - iSplitL.
      by iApply "HΦ".
    iFrame "Hverify".
    iSplitL; first by iApply ("Hvlow" with "Hφ").
    clear p Φ. iIntros (p v) "!#". iIntros (Φ) "Hv HΦ".
    wp_apply ("Hsign" with "* Hv"). iIntros (?) "[? _]".
    by iApply "HΦ".
  Qed.

  Definition is_encrypt (φ : val → iProp Σ) (encrypt : val) : iProp Σ :=
    (∀ p v, {{{ φ v }}} encrypt v @ p; ⊤ {{{ v', RET v'; low v' }}})%I.
  Definition is_decrypt (φ : val → iProp Σ) (decrypt : val) : iProp Σ :=
    (∀ v', {{{ low v' }}} decrypt v' ?{{{ v, RET v; low v ∨ φ v }}})%I.

  Lemma encryption_scheme_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_key_pair () @ p; ⊤
    {{{ v1 v2, RET (v1, v2); low v1 ∗ is_encrypt φ v1 ∗ is_decrypt φ v2 }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam.
    wp_apply (make_sealer_unsealer_spec S N _ (λ v, (low v ∨ φ v)%I)
      with "Hh"); first done. iIntros (k γ) "#Hk". wp_let.
    wp_apply (seal_spec with "Hk"). iIntros (enc) "[Helow #Henc]".
    wp_apply (unseal_low_spec with "Hk"). iIntros (dec) "[_ Hdec]".
      wp_value.
    iApply "HΦ". iFrame "Hdec".
    iSplitL; first by iApply "Helow"; iAlways; iIntros; iLeft.
    clear p Φ. iIntros (p v) "!#". iIntros (Φ) "Hv HΦ".
    wp_apply ("Henc" with "* [Hv]"); first by iRight. iIntros (?) "[? _]".
    by iApply "HΦ".
  Qed.
End pk_proof.

(** * Simple security protocol *)
(**
	The following example regards its context as an adversarial
	network. The send and receive functions transmit
	high-integrity locations containing even numbers.
*)
Section proto_code.
  Context {SI : SealingImpl}.

  Definition protocol : expr :=
    let: "k" := make_key_pair () in
    let: "sign" := Fst "k" in let: "verify" := Snd "k" in
    let: "k" := make_key_pair () in
    let: "enc" := Fst "k" in let: "dec" := Snd "k" in
    let: "send" := λ: "x", assume: even: "x" ;; "sign" ("enc" (ref "x")) in
    let: "recv" := λ: "m", assert: even: ! ("dec" ("verify" "m")) in
    ("send", "recv").
End proto_code.

Section proto_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.
  Implicit Types l : loc.

  Let φenc (v : val) : iProp Σ := (∃ l n, ⌜v = l%V⌝ ∗ l ↦ #n ∗ ⌜Z.even n⌝)%I.
  Let φsign (v' : val) : iProp Σ := (
    ∃ v,
  )%I.
  Lemma protocol_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} protocol {{{ v, RET v; low v }}}.
  Proof.
    iIntros (Φ) "HΦ". rewrite/protocol.
    wp_apply (signature_scheme_spec with "

(*
	PDS: We need a signature/encryption scheme client.
*)

Section ClosedProofs.
  Import lock.

  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; proof.sealingΣ; spin_lock.lockΣ ].
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
