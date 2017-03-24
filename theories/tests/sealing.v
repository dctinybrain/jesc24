From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import sealing assume.
From iris.heap_lang.lib Require lock spin_lock.
From iris.tests Require Import even.
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
	Other than the snapshot operation, this is Morris' example.
	Snapshots are useful at the boundary with adversarial code.
*)
Section intervals_code.
  Context {SI : SealingImpl}.

  Definition intervals : val := λ: <>,
    let: "p" := make_seal () in
    let: "seal" := Fst "p" in let: "unseal" := Snd "p" in
    let: "make_int" := λ: "n1" "n2",
      "seal" (if: "n1" ≤ "n2" then ("n1", "n2") else ("n2", "n1"))
    in
    let: "snap" := λ: "i", "seal" ("unseal" "i") in
    let: "min" := λ: "i", Fst ("unseal" "i") in
    let: "max" := λ: "i", Snd ("unseal" "i") in
    let: "sum" :=
      λ: "i", let: "x" := "unseal" "i" in
      λ: "j", let: "y" := "unseal" "j" in
      "seal" (Fst "x" + Fst "y", Snd "x" + Snd "y")
    in ("make_int", "snap", "min", "max", "sum").
End intervals_code.

Section intervals_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).
  Implicit Types f v : val.
  Implicit Types n : Z.

  (** Definitions *)

  Definition intφ (v : val) : iProp Σ :=
    (∃ n1 n2, ⌜v = (#n1, #n2)%V⌝ ∗ ⌜n1 ≤ n2⌝)%I.

  Record name : Type := { nameS : intf.name S; seal : val; unseal : val }.

  Definition ctx γ : iProp Σ := (
    is_seal S (nameS γ) (seal γ) intφ ∗
    is_unseal S (nameS γ) (unseal γ) intφ
  )%I.

  Definition is_interval γ n1 n2 v : iProp Σ :=
    (ctx γ ∗ is_sealed S (nameS γ) (#n1, #n2)%V v intφ)%I.

  Definition is_make_int γ v : iProp Σ := (
    ctx γ ∗
    ⌜v = LamV "n1" (λ: "n2",
      (seal γ) (if: "n1" ≤ "n2" then ("n1", "n2") else ("n2", "n1")))⌝
  )%I.
  Definition is_make_int' γ n1 v : iProp Σ := (
    ctx γ ∗
    ⌜v = LamV "n2" (
      (seal γ) (if: #n1 ≤ "n2" then (#n1, "n2") else ("n2", #n1)))%E⌝
  )%I.

  Definition is_snap γ v : iProp Σ :=
    (ctx γ ∗ ⌜v = LamV "i" ((seal γ) ((unseal γ) "i"))⌝)%I.
  Definition is_min γ v : iProp Σ :=
    (ctx γ ∗ ⌜v = LamV "i" (Fst ((unseal γ) "i"))⌝)%I.
  Definition is_max γ v : iProp Σ :=
    (ctx γ ∗ ⌜v = LamV "i" (Snd ((unseal γ) "i"))⌝)%I.

  Definition is_sum γ v : iProp Σ := (
    ctx γ ∗
    ⌜v = LamV "i" (
      let: "x" := (unseal γ) "i" in
      λ: "j", let: "y" := (unseal γ) "j" in
      (seal γ) (Fst "x" + Fst "y", Snd "x" + Snd "y"))⌝
  )%I.
  Definition is_sum' γ n1 n2 v : iProp Σ := (
    ctx γ ∗ ⌜n1 ≤ n2⌝ ∗
    ⌜v = LamV "j" (
      let: "y" := (unseal γ) "j" in
      (seal γ) (Fst (#n1, #n2) + Fst "y", Snd (#n1, #n2) + Snd "y"))⌝
  )%I.

  (** Structure *)

  Instance intφ_persistent v : PersistentP (intφ v).
  Proof. apply _. Qed.
  Global Instance is_interval_persistent γ n1 n2 v :
    PersistentP (is_interval γ n1 n2 v).
  Proof. apply _. Qed.
  Global Instance is_make_int_persistent γ v :
    PersistentP (is_make_int γ v).
  Proof. apply _. Qed.
  Global Instance is_make_int'_persistent γ v :
    PersistentP (is_make_int γ v).
  Proof. apply _. Qed.
  Global Instance is_snap_persistent γ v : PersistentP (is_snap γ v).
  Proof. apply _. Qed.
  Global Instance is_min_persistent γ v : PersistentP (is_min γ v).
  Proof. apply _. Qed.
  Global Instance is_max_persistent γ v : PersistentP (is_max γ v).
  Proof. apply _. Qed.
  Global Instance is_sum_persistent γ v : PersistentP (is_sum γ v).
  Proof. apply _. Qed.
  Global Instance is_sum'_persistent γ n1 n2 v :
    PersistentP (is_sum' γ n1 n2 v).
  Proof. apply _. Qed.

  (** The [intervals] function *)

  Lemma intervals_spec N p :
    heapN ⊥ N →
    {{{ heap_ctx }}} intervals () @ p; ⊤
    {{{ (make_int snap min max sum : val) γ,
        RET (make_int, snap, min, max, sum);
      is_make_int γ make_int ∗ is_snap γ snap ∗
      is_min γ min ∗ is_max γ max ∗ is_sum γ sum }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam.
    wp_apply (make_seal_spec S N _ intφ with "Hh"); first done.
      iIntros (seal unseal γS) "[Hs Hu]". wp_let. do 2!(wp_proj; wp_let).
      do 5!wp_let. set γ := {|nameS := γS; seal := seal; unseal := unseal |}.
    iApply ("HΦ" $! _ _ _ _ _ γ). iAssert (ctx γ) with "[$Hs $Hu]" as "#Hctx".
    iFrame "Hctx Hctx Hctx Hctx Hctx". by auto.
  Qed.

  (** Trivial properties of [is_interval] *)

  Lemma interval_inv γ n1 n2 v : is_interval γ n1 n2 v -∗ ⌜n1 ≤ n2⌝.
  Proof.
    iIntros "[_ Hv]". iDestruct (sealed_inv with "Hv") as (n'1 n'2) "[EQ %]".
    by iDestruct "EQ" as %[=<-<-].
  Qed.

  Lemma interval_low γ n1 n2 v : is_interval γ n1 n2 v -∗ low v.
  Proof. iIntros "[_ Hv]". by iApply (sealed_low with "Hv"). Qed.

  (** The make interval function *)

  Lemma make_int_spec p γ mk n1 :
    {{{ is_make_int γ mk }}} mk #n1 @ p; ⊤
    {{{ f, RET f; is_make_int' γ n1 f }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by iApply ("HΦ" with "[$Hctx]").
  Qed.

  (**
	With typecasts in make interval, we could show
<<
	{{{ is_make_int γ mk }}} mk v1
	?{{{ f n1, RET f; is_make_int' γ n1 f }}}
>>
  *)

  Notation MakeIntPost γ n1 n2 v := (
    is_interval γ (Z.min n1 n2) (Z.max n1 n2) v
  )%I (only parsing).

  Lemma make_int'_body p γ n1 n2 :
    {{{ ctx γ }}}
      (seal γ) (if: #n1 ≤ #n2 then (#n1, #n2) else (#n2, #n1)) @ p; ⊤
    {{{ v, RET v; MakeIntPost γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "#Hctx HΦ". iDestruct (persistentP with "Hctx") as "[#Hs _]".
      rewrite/is_interval.
    wp_op=>[?|/Z.lt_le_incl ?]; wp_if.
    - wp_apply (seal_spec with "[$Hs]"); first by iAlways; iExists n1, n2; auto.
        iIntros (v') "#Hv'".
      iApply ("HΦ" with "[$Hctx]"). by rewrite (Z.min_l n1) // (Z.max_r _ n2).
    - wp_apply (seal_spec with "[$Hs]"); first by iAlways; iExists n2, n1; auto.
        iIntros (v') "#Hv'".
      iApply ("HΦ" with "[$Hctx]"). by rewrite (Z.min_r _ n2) // (Z.max_l n1).
  Qed.

  Lemma make_int'_spec p γ mk n1 n2 :
    {{{ is_make_int' γ n1 mk }}} mk #n2 @ p; ⊤
    {{{ v, RET v; MakeIntPost γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by wp_apply (make_int'_body with "Hctx [$HΦ]").
  Qed.

  Lemma make_int'_body_any γ n1 v2 :
    {{{ ctx γ }}}
      (seal γ) (if: #n1 ≤ v2 then (#n1, v2) else (v2, #n1))
    ?{{{ v n2, RET v; MakeIntPost γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "Hctx HΦ".
    case: (decide (is_int (of_val v2)))=>Hv2; last by wp_apply wp_stuck_lt_r.
      destruct (is_int_val _ Hv2) as (n2&->).
    wp_apply (make_int'_body with "Hctx"). iIntros (v) "Hv".
    by iApply ("HΦ" $! _ n2 with "Hv").
  Qed.

  Lemma make_int'_any_spec γ mk n1 v2 :
    {{{ is_make_int' γ n1 mk }}} mk v2
    ?{{{ v n2, RET v; MakeIntPost γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by wp_apply (make_int'_body_any with "Hctx [$HΦ]").
  Qed.

  Lemma make_int'_low γ mk n1 : is_make_int' γ n1 mk -∗ low mk.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
    iIntros (v2 Φ) "_ HΦ". simpl_subst.
    wp_apply (make_int'_body_any with "Hctx"). iIntros (v ?) "[_ Hv]".
    iApply "HΦ". by iApply (sealed_low with "Hv").
  Qed.

  Lemma make_int_low γ mk : is_make_int γ mk -∗ low mk.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v1 Φ) "_ HΦ". simpl_subst. wp_value.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (v2 Φ) "_ HΦ". simpl_subst.
    case: (decide (is_int (of_val v1)))=>Hv1; last by wp_apply wp_stuck_lt_l.
      destruct (is_int_val _ Hv1) as (n1&->).
    wp_apply (make_int'_body_any with "Hctx"). iIntros (v n2) "[_ Hv]".
    iApply "HΦ". by iApply (sealed_low with "Hv").
  Qed.

  Lemma make_int_val p γ mk n1 n2 :
  {{{ is_make_int γ mk }}} mk #n1 #n2 @ p; ⊤
  {{{ v, RET v; MakeIntPost γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "Hmk HΦ".
    wp_apply (make_int_spec with "Hmk"). iIntros (f) "Hf".
    wp_apply (make_int'_spec with "[$Hf] [$HΦ]").
  Qed.

  (** Internal lemmas for unsealing intervals *)

  Lemma unseal_interval p γ n1 n2 v :
    {{{ is_interval γ n1 n2 v }}} (unseal γ) v @ p; ⊤
    {{{ RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "#[[_ Hu] Hv] HΦ".
      iDestruct (sealed_inv with "Hv") as (??) "[EQ %]".
      iDestruct "EQ" as %[=<-<-].
    wp_apply (unseal_spec with "[$Hu $Hv]"). iIntros "_".
    by iApply ("HΦ" with "[%]").
  Qed.

  Lemma unseal_interval_low γ v' :
    {{{ ctx γ ∗ low v' }}} (unseal γ) v'
    ?{{{ n1 n2, RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "[[_ Hu] Hv'] HΦ".
    wp_apply (unseal_low_spec with "[$Hu $Hv']").
      iIntros (v). iDestruct 1 as (n1 n2) "[%%]". subst.
    by iApply ("HΦ" with "[%]").
  Qed.

  (** The snapshot function *)

  Lemma snap_spec p γ snap n1 n2 v :
    {{{ is_snap γ snap ∗ is_interval γ n1 n2 v }}} snap v @ p; ⊤
    {{{ v', RET v'; is_interval γ n1 n2 v' }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] Hv] HΦ".
      iDestruct (persistentP with "Hctx") as "[#Hs _]". subst. wp_lam.
    wp_apply (unseal_interval with "Hv"). iIntros "%". wp_value.
    wp_apply (seal_spec with "[$Hs]");
      first by iAlways; iExists n1, n2; iFrame "%". iIntros (v') "Hv'".
    by iApply ("HΦ" with "[$Hctx $Hv']").
  Qed.

  Lemma snap_body γ v :
    {{{ ctx γ ∗ low v }}} (seal γ) ((unseal γ) v)
    ?{{{ v' n1 n2, RET v'; is_interval γ n1 n2 v' }}}.
  Proof.
    iIntros (Φ) "[#Hctx Hv] HΦ".
      iDestruct (persistentP with "Hctx") as "[#Hs _]".
    wp_apply (unseal_interval_low with "[$Hctx $Hv]").
      iIntros (n1 n2) "%". wp_value.
    wp_apply (seal_spec with "[$Hs]");
      first by iAlways; iExists n1, n2; iFrame "%". iIntros (v') "Hv'".
    by iApply ("HΦ" with "[$Hctx $Hv']").
  Qed.

  Lemma snap_low_spec γ snap v :
    {{{ is_snap γ snap ∗ low v }}} snap v
    ?{{{ v' n1 n2, RET v'; is_interval γ n1 n2 v' }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv] HΦ". subst. wp_lam.
    by wp_apply (snap_body with "[$Hctx $Hv]").
  Qed.

  Lemma snap_low γ snap : is_snap γ snap -∗ low snap.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v Φ) "Hv HΦ". simpl_subst.
    wp_apply (snap_body with "[$Hctx $Hv]"). iIntros (v' n1 n2) "Hv'".
    iApply "HΦ". by iApply (interval_low with "Hv'").
  Qed.

  (** The min function *)

  Lemma min_spec p γ min n1 n2 v' :
    {{{ is_min γ min ∗ is_interval γ n1 n2 v' }}} min v' @ p; ⊤
    {{{ RET #n1; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv'"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_body γ v' :
    {{{ ctx γ ∗ low v' }}} Fst ((unseal γ) v') ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[Hctx Hv'] HΦ".
    wp_apply (unseal_interval_low with "[$Hctx $Hv']"). iIntros (n1 n2) "%".
      wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_low_spec γ min v' :
    {{{ is_min γ min ∗ low v' }}} min v' ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (min_body with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Lemma min_low γ min : is_min γ min -∗ low min.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (min_body with "[$Hctx $Hv']"). iIntros (n) "_".
    iApply "HΦ". by simpl_low.
  Qed.

  (** The max function *)

  Lemma max_spec p γ max n1 n2 v' :
    {{{ is_max γ max ∗ is_interval γ n1 n2 v' }}} max v' @ p; ⊤
    {{{ RET #n2; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv'"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma max_body γ v' :
    {{{ ctx γ ∗ low v' }}} Snd ((unseal γ) v') ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[Hctx Hv'] HΦ".
    wp_apply (unseal_interval_low with "[$Hctx $Hv']"). iIntros (n1 n2) "%".
      wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma max_low_spec γ max v' :
    {{{ is_max γ max ∗ low v' }}} max v' ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (max_body with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Lemma max_low γ max : is_max γ max -∗ low max.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (max_body with "[$Hctx $Hv']"). iIntros (n) "_".
    iApply "HΦ". by simpl_low.
  Qed.

  (** The sum function *)

  Lemma sum_body p γ n1 n2 :
    n1 ≤ n2 →
    {{{ ctx γ }}}
      let: "x" := (#n1, #n2) in λ: "j", let: "y" := (unseal γ) "j" in
      (seal γ) (Fst "x" + Fst "y", Snd "x" + Snd "y") @ p; ⊤
    {{{ f, RET f; is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (? Φ) "Hctx HΦ". wp_let.
    iApply ("HΦ" with "[$Hctx]"). by iFrame "%".
  Qed.

  Lemma sum_spec p γ sum n1 n2 v' :
    {{{ is_sum γ sum ∗ is_interval γ n1 n2 v' }}} sum v' @ p; ⊤
    {{{ f, RET f; is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] Hv'] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv'"). iIntros "%".
    by wp_apply (sum_body with "Hctx").
  Qed.

  Lemma sum_low_spec γ sum v2 :
    {{{ is_sum γ sum ∗ low v2 }}} sum v2
    ?{{{ f n1 n2, RET f; is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] Hv2] HΦ". subst. wp_lam.
    wp_apply (unseal_interval_low with "[$Hctx $Hv2]"). iIntros (??) "%".
    wp_apply (sum_body with "Hctx"); first done. iIntros (f) "Hf".
    by iApply ("HΦ" with "Hf").
  Qed.

  Lemma sum'_body p γ n1 n2 n'1 n'2 :
    n1 ≤ n2 → n'1 ≤ n'2 →
    {{{ ctx γ }}}
      let: "y" := (#n'1, #n'2) in
      (seal γ) (Fst (#n1, #n2) + Fst "y", Snd (#n1, #n2) + Snd "y") @ p; ⊤
    {{{ v, RET v; is_interval γ (n1 + n'1) (n2 + n'2) v }}}.
  Proof.
    iIntros (?? Φ) "#[Hs Hu] HΦ". wp_let.
      do 2!wp_proj. wp_op. do 2!wp_proj. wp_op. wp_value.
    wp_apply (seal_spec with "[$Hs]").
    - iAlways. iExists _, _. iSplit. done. by iPureIntro; lia.
    - iIntros (v) "Hv". by iApply ("HΦ" with "[$Hs $Hu $Hv]").
  Qed.

  Lemma sum'_spec p γ n1 n2 sum n'1 n'2 v2 :
    {{{ is_sum' γ n1 n2 sum ∗ is_interval γ n'1 n'2 v2 }}}
      sum v2 @ p; ⊤
    {{{ v, RET v; is_interval γ (n1 + n'1) (n2 + n'2) v }}}.
  Proof.
    iIntros (Φ) "[(#Hctx & % & %) Hv2] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv2"). iIntros "%".
    by wp_apply (sum'_body with "Hctx").
  Qed.

  Lemma sum'_body_low γ n1 n2 v2 :
    n1 ≤ n2 →
    {{{ ctx γ ∗ low v2 }}}
      let: "y" := (unseal γ) v2 in
      (seal γ) (Fst (#n1, #n2) + Fst "y", Snd (#n1, #n2) + Snd "y")
    ?{{{ v n'1 n'2, RET v; is_interval γ n'1 n'2 v }}}.
  Proof.
    iIntros (? Φ) "[#Hctx Hv2] HΦ".
    wp_apply (unseal_interval_low with "[$Hctx $Hv2]"). iIntros (m1 m2) "%".
    wp_apply (sum'_body with "Hctx")=>//. iIntros (v) "Hv".
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma sum'_low_spec γ n1 n2 sum v2 :
    {{{ is_sum' γ n1 n2 sum ∗ low v2 }}} sum v2
    ?{{{ v n'1 n'2, RET v; is_interval γ n'1 n'2 v }}}.
  Proof.
    iIntros (Φ) "[(#Hctx & % & %) Hv2] HΦ". subst. wp_lam.
    by wp_apply (sum'_body_low with "[$Hctx $Hv2]").
  Qed.

  Lemma sum'_low γ n1 n2 sum : is_sum' γ n1 n2 sum -∗ low sum.
  Proof.
    iIntros "(#Hctx & % & %)". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v2 Φ) "Hv2 HΦ". simpl_subst.
    wp_apply (sum'_body_low with "[$Hctx $Hv2]")=>//.
      iIntros (v n'1 n'2) "Hv".
    iApply "HΦ". by iApply (interval_low with "Hv").
  Qed.

  Lemma sum_low γ sum : is_sum γ sum -∗ low sum.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v1 Φ) "Hv1 HΦ". simpl_subst.
    wp_apply (unseal_interval_low with "[$Hctx $Hv1]"). iIntros (??) "%".
    wp_apply (sum_body with "Hctx"); first done. iIntros (f) "Hf".
    rewrite sum'_low. by iApply "HΦ".
  Qed.

  Lemma sum_val p γ sum n1 n2 v1 n'1 n'2 v2 :
    {{{ is_sum γ sum ∗ is_interval γ n1 n2 v1 ∗ is_interval γ n'1 n'2 v2 }}}
      sum v1 v2 @ p; ⊤
    {{{ v, RET v; is_interval γ (n1 + n'1) (n2 + n'2) v }}}.
  Proof.
    iIntros (Φ) "(Hsum & Hv1 & Hv2) HΦ".
    wp_apply (sum_spec with "[$Hsum $Hv1]"). iIntros (f) "Hf".
    by wp_apply (sum'_spec with "[$Hf $Hv2]").
  Qed.
End intervals_proof.
Typeclasses Opaque is_interval is_make_int is_make_int'
  is_snap is_min is_max is_sum is_sum'.

(** * Simple intervals client *)
Section intervals_client_code.
  Context {SI : SealingImpl}.

  Definition interval_client : expr :=
    let: "cap" := intervals () in
    let: "make_int" := Fst $ Fst $ Fst $ Fst "cap" in
    let: "snap" := Snd $ Fst $ Fst $ Fst "cap" in
    let: "min" := Snd $ Fst $ Fst "cap" in
    let: "max" := Snd $ Fst "cap" in
    let: "sum" := Snd "cap" in
    let: "i100" := "sum" ("make_int" #1 #0) ("make_int" #(-1) #100) in
    assert: ("min" "i100" = #-1) ;; assert: ("max" "i100" = #101) ;;
    let: "use" := λ: "i",
      let: "i" := "snap" "i" in
      assert: ("min" "i" ≤ "max" "i") ;;
      "sum" "i" "i100"
    in
    ("use", "cap").
End intervals_client_code.

Section intervals_client_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).

  Lemma interval_client_spec N :
    heapN ⊥ N →
    {{{ heap_ctx }}} interval_client {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/interval_client.
    wp_apply (intervals_spec S with "Hh")=>//.
      iIntros (mk snap min max sum γ)
        "#(Hmk & Hsnap & Hmin & Hmax & Hsum)".
      wp_let. do 4!wp_proj; wp_let. do 4!wp_proj; wp_let.
      do 3!wp_proj; wp_let. do 2!wp_proj; wp_let. wp_proj; wp_let.
    (** The interval [-1, 101] *)
    wp_apply (make_int_val with "Hmk"). iIntros (i1) "Hi1".
    wp_apply (sum_spec with "[$Hsum $Hi1]"). iIntros (f) "Hf".
    wp_apply (make_int_val with "Hmk"). iIntros (i2) "Hi2".
    wp_apply (sum'_spec with "[$Hf $Hi2]"). iIntros (i100) "#Hi100". wp_let.
    wp_apply (min_spec with "[$Hmin $Hi100]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq.
    wp_apply (max_spec with "[$Hmax $Hi100]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq. wp_let. clear i1 f i2.
    iApply "HΦ". clear Φ. simpl_low. iSplitL; iNext.
    (** The use function is low. *)
    { rewrite low_rec. iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst.
      wp_apply (snap_low_spec with "[$Hsnap $Hv]"). iIntros (i n1 n2) "#Hi".
        wp_let.
      wp_apply (min_spec with "[$Hmin $Hi]"). iIntros "_".
      wp_apply (max_spec with "[$Hmax $Hi]"). iIntros "_".
        iDestruct (interval_inv with "Hi") as "%".
      wp_apply wp_assert. wp_op=>?; last by exfalso; lia.
        iSplit; first done. iNext. wp_seq.
      wp_apply (sum_val with "[$Hsum $Hi $Hi100]"). iIntros (?) "?".
      iApply "HΦ". by iApply interval_low. }
    iSplitL; iNext; last by iApply (sum_low with "Hsum").
    iSplitL; iNext; last by iApply (max_low with "Hmax").
    iSplitL; iNext; last by iApply (min_low with "Hmin").
    iSplitL; iNext; last by iApply (snap_low with "Hsnap").
    by iApply (make_int_low with "Hmk").
  Qed.
End intervals_client_proof.

(** * Public-key interfaces for sealer-unsealer pairs *)
(**
	When instantiated with suitable representation invariants,
	sealer-unsealer pairs satisfy natural interfaces for
	asymmetric signature and encryption schemes.
*)
Section pk_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.

  Section sig_triples.
    Context (φ : val → iProp Σ) (signat : val → val → iProp Σ).
    Definition is_sign (sign : val) : iProp Σ :=
      (∀ p v, {{{ φ v }}} sign v @ p; ⊤ {{{ v', RET v'; low v' ∗ □ signat v v' }}})%I.
    Definition verify_sig (verify : val) : iProp Σ :=
      (∀ p v v', {{{ signat v v' }}} verify v' @ p; ⊤ {{{ RET v; φ v }}})%I.
    Definition verify_low (verify : val) : iProp Σ :=
      (∀ v', {{{ low v' }}} verify v' ?{{{ v, RET v; φ v }}})%I.
    Definition is_verify (v : val) : iProp Σ :=
      (low v ∗ verify_sig v ∗ verify_low v)%I.
    Global Instance is_sign_persistent v : PersistentP (is_sign v) := _.
    Global Instance is_verify_persistent v : PersistentP (is_verify v) := _.
  End sig_triples.

  Lemma signature_scheme_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx ∗ □ (∀ v, φ v -∗ low v) }}} make_seal () @ p; ⊤
    {{{ v1 v2 sig, RET (v1, v2); is_sign φ sig v1 ∗ is_verify φ sig v2 }}}.
  Proof.
    iIntros (? Φ) "#[Hh Hφ] HΦ".
    wp_apply (make_seal_spec S N _ φ with "Hh"); first done.
      iIntros (sign verify γ) "#[Hsign Hverify]".
    iApply ("HΦ" $! _ _ (λ v v', is_sealed S γ v v' φ)). clear p Φ.
    iSplitL; [| iSplitL; [| iSplitL]].
    - iIntros (p v) "!#". iIntros (Φ) "#Hv HΦ".
      wp_apply (seal_spec with "[$Hsign Hv]"); first by iAlways.
        iIntros (v') "#Hv'".
      iApply "HΦ". iSplitL. by iApply sealed_low. by iAlways.
    - by iApply (unseal_low with "Hverify Hφ").
    - iIntros (p v v') "!#". iIntros (Φ) "#Hsig HΦ".
      wp_apply (unseal_spec with "[$Hverify $Hsig]"). iIntros "_".
      iApply "HΦ". by iApply (sealed_inv with "Hsig").
    - iIntros (v') "!#". iIntros (Φ) "Hsig HΦ".
      by wp_apply (unseal_low_spec with "[$Hverify $Hsig]").
  Qed.

  Section enc_triples.
    Context (φ : val → iProp Σ) (ctext : val → val → iProp Σ).
    Definition encrypt (enc : val) : iProp Σ :=
      (∀ p v, {{{ φ v }}} enc v @ p; ⊤ {{{ v', RET v'; low v' ∗ □ ctext v v' }}})%I.
    Definition is_encrypt (v : val) : iProp Σ := (low v ∗ encrypt v)%I.
    Definition decrypt_ctext (dec : val) : iProp Σ :=
      (∀ p v v', {{{ ctext v v' }}} dec v' @ p; ⊤ {{{ RET v; low v ∨ φ v }}})%I.
    Definition decrypt_low (dec : val) : iProp Σ :=
      (∀ v', {{{ low v' }}} dec v' ?{{{ v, RET v; low v ∨ φ v }}})%I.
    Definition is_decrypt (v : val) : iProp Σ :=
      (decrypt_ctext v ∗ decrypt_low v)%I.
    Global Instance is_encrypt_persistent v : PersistentP (is_encrypt v) := _.
    Global Instance is_decrypt_persistent v : PersistentP (is_decrypt v) := _.
  End enc_triples.

  Lemma encryption_scheme_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_seal () @ p; ⊤
    {{{ v1 v2 ctext, RET (v1, v2); is_encrypt φ ctext v1 ∗ is_decrypt φ ctext v2 }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". set φenc := (λ v, (low v ∨ φ v)%I).
    wp_apply (make_seal_spec S N _ φenc with "Hh");
      first done. iIntros (enc dec γ) "#[Henc Hdec]".
    iApply ("HΦ" $! _ _ (λ v v', is_sealed S γ v v' φenc)). clear p Φ.
    iSplitL; iSplitL.
    - iApply (seal_low with "Henc []"). iAlways. iIntros (v) "Hv". by iLeft.
    - iIntros (p v) "!#". iIntros (Φ) "#Hv HΦ".
      wp_apply (seal_spec with "[$Henc Hv]"); first by iAlways; iRight.
        iIntros (v') "#Hv'".
      iApply "HΦ". iSplitL. by iApply sealed_low. by iAlways.
    - iIntros (p v v') "!#". iIntros (Φ) "#Hv HΦ".
      wp_apply (unseal_spec with "[$Hdec $Hv]"). iIntros "_".
      iApply "HΦ". by iApply (sealed_inv with "Hv").
    - iIntros (v') "!#". iIntros (Φ) "Hv' HΦ".
      by wp_apply (unseal_low_spec with "[$Hdec $Hv']").
  Qed.
End pk_proof.

(** * Simple security protocol *)
(**
	The following example regards its context as an adversarial
	network. The send and receive functions transmit
	high-integrity locations, using sealer-unsealer pairs for
	secrecy and integrity.
*)
Section pk_client.
  Context {SI : SealingImpl}.

  Definition pk_client : expr :=
    let: "ek" := make_seal () in
    let: "enc" := Fst "ek" in let: "dec" := Snd "ek" in
    let: "sk" := make_seal () in
    let: "sign" := Fst "sk" in let: "verify" := Snd "sk" in
    let: "send" := λ: "x", assume_even "x" ;; "sign" ("enc" (ref "x")) in
    let: "recv" := λ: "m", assert_even (! ("dec" ("verify" "m"))) in
    ("send", "recv").
End pk_client.

Section pk_client_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.
  Implicit Types l : loc.

  Let Nloc : namespace := N .@ "loc".
  Let Nseal : namespace := N .@ "seal".

  Let φenc (v : val) : iProp Σ :=
    (∃ l v', ⌜v = l%V⌝ ∗ is_even v' ∗ inv Nloc (l ↦ v'))%I.
  Let φsign (ctext : val → val → iProp Σ) (v' : val) : iProp Σ :=
    (low v' ∗ □ ∃ v, φenc v ∗ ctext v v')%I.

  Lemma pk_client_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} pk_client {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/pk_client.
    wp_apply (encryption_scheme_spec S Nseal _ φenc with "Hh");
      first by solve_ndisj.
      iIntros (enc dec ctext) "#[[Hlowenc Henc] [Hdectext Hdeclow]]".
      wp_let. do 2!(wp_proj; wp_let).
    wp_apply (signature_scheme_spec S Nseal _ (φsign ctext) with "[$Hh]");
      [by solve_ndisj | by iAlways; iIntros (?) "[? _]" |].
      iIntros (sign ver sig) "#[Hsign (Hlowv & Hversig & Hverlow)]".
      wp_let. do 2!(wp_proj; wp_let). do 2!wp_let.
    iApply "HΦ". clear Φ. simpl_low. iNext.
    iSplitL; rewrite low_rec; iAlways; iNext; iIntros (v0 Φ) "#Hv0 HΦ";
      simpl_subst.
    - wp_apply assume_even_spec. iIntros "Hev". wp_let.
        wp_alloc l as "Hl".
      iMod (inv_alloc Nloc _ (l ↦ v0)%I with "[$Hl]") as "#Hinv".
      iAssert (φenc (LocV l)) with "[Hev]" as "#Hφenc";
        first by iExists l, v0; iFrame "Hev Hinv".
      wp_apply ("Henc" with "* Hφenc").  iIntros (v1) "[#Hlowv1 #Hv1]".
      wp_apply ("Hsign" with "* [$Hlowv1]");
        first by iAlways; iExists (LocV l); iFrame "Hφenc Hv1".
        iIntros (v2) "[? _]".
      by iApply "HΦ".
    - wp_apply ("Hverlow" $! v0 with "Hv0"). iIntros (v1) "[Hlowv1 Hv1]".
        iDestruct "Hv1" as (v2) ">[Hφenc Hv1]".
      wp_apply ("Hdectext" with "* Hv1"). iIntros "_".
        iDestruct "Hφenc" as (l v3) "(% & #Hev & Hinv)". subst.
        wp_bind (! _)%E.
      iInv Nloc as "Hl" "Hcl". wp_load. iMod ("Hcl" with "[$Hl]") as "_".
        iModIntro.
(* PDS: generalize assert_even_spec *)
      wp_apply (wp_forget_progress progress).
      wp_apply (assert_even_spec with "Hev"). iIntros "_".
      iApply "HΦ". by iApply is_even_low.
  Qed.
End pk_client_proof.

Section ClosedProofs.
  Import lock.

  Let lock : LockImpl := spin_lock.spin.
  Let sealing : SealingImpl := @code.sealing lock.
  Let interval_client : expr := @interval_client sealing.

  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; proof.sealingΣ; spin_lock.lockΣ ].

  Lemma interval_client_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C interval_client], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.spin_lock. set S := proof.sealing L.
    iApply (interval_client_spec S N with "Hh"); auto with ndisj.
  Qed.

  Let pk_client : expr := @pk_client sealing.
  Lemma pk_client_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C pk_client], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.spin_lock. set S := proof.sealing L.
    iApply (pk_client_spec S N with "Hh"); auto with ndisj.
  Qed.
End ClosedProofs.

Print Assumptions interval_client_safe.
Print Assumptions pk_client_safe.
