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
	Snapshots are useful (with weak unsealing) at the boundary
	with adversarial code.
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

  Definition is_intervals γ (mk snap min max sum : val) : iProp Σ := (
    is_make_int γ mk ∗ is_snap γ snap ∗
    is_min γ min ∗ is_max γ max ∗ is_sum γ sum
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
  Global Instance is_intervals_persistent γ mk snap min max sum :
    PersistentP (is_intervals γ mk snap min max sum).
  Proof. apply _. Qed.

  (** The [intervals] function *)

  Lemma intervals_spec N p :
    heapN ⊥ N →
    {{{ heap_ctx }}} intervals () @ p; ⊤
    {{{ v1 v2 v3 v4 v5 γ, RET (v1, v2, v3, v4, v5);
      is_intervals γ v1 v2 v3 v4 v5 }}}.
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

  Lemma interval_agree γ n1 n2 n'1 n'2 v :
    is_interval γ n1 n2 v ∗ is_interval γ n'1 n'2 v
    ⊢ ⌜n1 = n'1⌝ ∗ ⌜n2 = n'2⌝.
  Proof.
    iIntros "[[_ Hv] [_ H'v]]".
    iDestruct (sealed_agree with "[$Hv $H'v]") as %[=->->]. by auto.
  Qed.

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

  Lemma unseal_interval_any γ v `{!strong_unsealing S} :
    {{{ ctx γ }}} (unseal γ) v
    ?{{{ n1 n2, RET (#n1, #n2); ⌜n1 ≤ n2⌝ ∗ is_interval γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "#Hctx HΦ".
      iDestruct (persistentP with "Hctx") as "[_ >Hu]".
    wp_apply (unseal_any_spec with "Hu"). iIntros (?) "Hv".
      iDestruct (sealed_inv with "Hv") as (n1 n2) "[%%]". subst.
    by iApply ("HΦ" with "[$Hctx $Hv]").
  Qed.

  Lemma unseal_interval_low γ v `{!weak_unsealing S} :
    {{{ ctx γ ∗ low v }}} (unseal γ) v
    ?{{{ n1 n2, RET (#n1, #n2); ⌜n1 ≤ n2⌝ }}}.
  Proof.
    iIntros (Φ) "[[_ Hu] Hv] HΦ".
    wp_apply (unseal_low_spec with "[$Hu $Hv]").
      iIntros (?). iDestruct 1 as (n1 n2) "[%%]". subst.
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

  (**
	While the following is sound, [strong_unsealing] obviates
	snapshots.
  *)
  Lemma snap_any_spec γ snap v `{!strong_unsealing S} :
    {{{ is_snap γ snap }}} snap v
    ?{{{ v' n1 n2, RET v'; is_interval γ n1 n2 v' }}}.
  Proof.
    iIntros (Φ) "[#Hctx %] HΦ". subst. wp_lam.
      iDestruct (persistentP with "Hctx") as "[#Hs _]".
    wp_apply (unseal_interval_any with "Hctx"). iIntros (n1 n2) "[% Hv]".
      wp_value.
    wp_apply (seal_spec with "[$Hs]");
      first by iAlways; iExists n1, n2; iFrame "%". iIntros (v') "Hv'".
    by iApply ("HΦ" with "[$Hctx $Hv']").
  Qed.

  Lemma snap_body_low γ v `{!weak_unsealing S} :
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

  Lemma snap_low_spec γ snap v `{!weak_unsealing S} :
    {{{ is_snap γ snap ∗ low v }}} snap v
    ?{{{ v' n1 n2, RET v'; is_interval γ n1 n2 v' }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv] HΦ". subst. wp_lam.
    by wp_apply (snap_body_low with "[$Hctx $Hv]").
  Qed.

  Lemma snap_low γ snap `{!weak_unsealing S} :
    is_snap γ snap -∗ low snap.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v Φ) "Hv HΦ". simpl_subst.
    wp_apply (snap_body_low with "[$Hctx $Hv]"). iIntros (v' n1 n2) "Hv'".
    iApply "HΦ". by iApply (interval_low with "Hv'").
  Qed.

  (** The min function *)

  Lemma min_spec p γ min n1 n2 v :
    {{{ is_min γ min ∗ is_interval γ n1 n2 v }}} min v @ p; ⊤
    {{{ RET #n1; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv"). iIntros "%". wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_any_spec γ min v `{!strong_unsealing S} :
    {{{ is_min γ min }}} min v
    ?{{{ n1 n2, RET #n1; is_interval γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    wp_apply (unseal_interval_any with "Hctx"). iIntros (n1 n2) "[% Hv]".
      wp_proj.
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma min_body_low γ v' `{!weak_unsealing S} :
    {{{ ctx γ ∗ low v' }}} Fst ((unseal γ) v') ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[Hctx Hv'] HΦ".
    wp_apply (unseal_interval_low with "[$Hctx $Hv']"). iIntros (n1 n2) "%".
      wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma min_low_spec γ min v' `{!weak_unsealing S} :
    {{{ is_min γ min ∗ low v' }}} min v' ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (min_body_low with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Lemma min_low γ min `{!weak_unsealing S} :
    is_min γ min -∗ low min.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (min_body_low with "[$Hctx $Hv']"). iIntros (n) "_".
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

  Lemma max_any_spec γ max v `{!strong_unsealing S} :
    {{{ is_max γ max }}} max v
    ?{{{ n1 n2, RET #n2; is_interval γ n1 n2 v }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    wp_apply (unseal_interval_any with "Hctx"). iIntros (n1 n2) "[% Hv]".
      wp_proj.
    by iApply ("HΦ" with "Hv").
  Qed.

  Lemma max_body_low γ v' `{!weak_unsealing S} :
    {{{ ctx γ ∗ low v' }}} Snd ((unseal γ) v') ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[Hctx Hv'] HΦ".
    wp_apply (unseal_interval_low with "[$Hctx $Hv']"). iIntros (n1 n2) "%".
      wp_proj.
    by iApply "HΦ".
  Qed.

  Lemma max_low_spec γ max v' `{!weak_unsealing S} :
    {{{ is_max γ max ∗ low v' }}} max v' ?{{{ n, RET #n; True }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (max_body_low with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Lemma max_low γ max `{!weak_unsealing S} :
    is_max γ max -∗ low max.
  Proof.
    iIntros "[#Hctx %]". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v' Φ) "Hv' HΦ". simpl_subst.
    wp_apply (max_body_low with "[$Hctx $Hv']"). iIntros (n) "_".
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

  Lemma sum_spec p γ sum n1 n2 v :
    {{{ is_sum γ sum ∗ is_interval γ n1 n2 v }}} sum v @ p; ⊤
    {{{ f, RET f; is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] Hv] HΦ". subst. wp_lam.
    wp_apply (unseal_interval with "Hv"). iIntros "%".
    by wp_apply (sum_body with "Hctx").
  Qed.

  Lemma sum_any_spec γ sum v `{!strong_unsealing S} :
    {{{ is_sum γ sum }}} sum v
    ?{{{ f n1 n2, RET f; is_interval γ n1 n2 v ∗ is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (Φ) "[#Hctx %] HΦ". subst. wp_lam.
    wp_apply (unseal_interval_any with "Hctx"). iIntros (??) "[% Hv]".
    wp_apply (sum_body with "Hctx"); first done. iIntros (f) "Hf".
    by iApply ("HΦ" with "[$Hv $Hf]").
  Qed.

  Lemma sum_low_spec γ sum v `{!weak_unsealing S} :
    {{{ is_sum γ sum ∗ low v }}} sum v
    ?{{{ f n1 n2, RET f; is_sum' γ n1 n2 f }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] Hv] HΦ". subst. wp_lam.
    wp_apply (unseal_interval_low with "[$Hctx $Hv]"). iIntros (??) "%".
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

  Lemma sum'_any_spec γ n1 n2 sum v2 `{!strong_unsealing S} :
    {{{ is_sum' γ n1 n2 sum }}}
      sum v2
    ?{{{ v n'1 n'2, RET v; is_interval γ n'1 n'2 v2
      ∗ is_interval γ (n1 + n'1) (n2 + n'2) v }}}.
  Proof.
    iIntros (Φ) "(#Hctx & % & %) HΦ". subst. wp_lam.
    wp_apply (unseal_interval_any with "Hctx"). iIntros (??) "[% Hv2]".
    wp_apply (sum'_body with "Hctx")=>//. iIntros (v) "Hv".
    by iApply ("HΦ" with "[$Hv2 $Hv]").
  Qed.

  Lemma sum'_body_low γ n1 n2 v2 `{!weak_unsealing S} :
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

  Lemma sum'_low_spec γ n1 n2 sum v2 `{!weak_unsealing S} :
    {{{ is_sum' γ n1 n2 sum ∗ low v2 }}} sum v2
    ?{{{ v n'1 n'2, RET v; is_interval γ n'1 n'2 v }}}.
  Proof.
    iIntros (Φ) "[(#Hctx & % & %) Hv2] HΦ". subst. wp_lam.
    by wp_apply (sum'_body_low with "[$Hctx $Hv2]").
  Qed.

  Lemma sum'_low γ n1 n2 sum `{!weak_unsealing S} :
    is_sum' γ n1 n2 sum -∗ low sum.
  Proof.
    iIntros "(#Hctx & % & %)". subst. rewrite low_rec. iAlways. iNext.
      iIntros (v2 Φ) "Hv2 HΦ". simpl_subst.
    wp_apply (sum'_body_low with "[$Hctx $Hv2]")=>//.
      iIntros (v n'1 n'2) "Hv".
    iApply "HΦ". by iApply (interval_low with "Hv").
  Qed.

  Lemma sum_low γ sum `{!weak_unsealing S} :
    is_sum γ sum -∗ low sum.
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

Section intervals_derived.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) `{!weak_unsealing S}.

  Lemma is_intervals_low γ mk snap min max sum :
    is_intervals S γ mk snap min max sum
    ⊢ low (mk, snap, min, max, sum)%V.
  Proof.
    iIntros "#(Hmk&Hsnap&Hmin&Hmax&Hsum)". simpl_low.
    iSplitL; iNext; last by iApply (sum_low with "Hsum").
    iSplitL; iNext; last by iApply (max_low with "Hmax").
    iSplitL; iNext; last by iApply (min_low with "Hmin").
    iSplitL; iNext; last by iApply (snap_low with "Hsnap").
    by iApply (make_int_low with "Hmk").
  Qed.
End intervals_derived.

(** * Simple interval client *)
(**
	The point of the following two expressions, which differ only
	in their "use" functions, is to demonstrate a practical cost
	of [weak_unsealing]. Put positively, [weak_interval_client]
	shows one technique—snapshots—to work around weak unsealing.

	With [strong_unsealing], we can verify both expressions. With
	[weak_unsealing], we can verify [weak_interval_client] (thanks
	to the snapshot).
*)
Section interval_client_code.
  Context {SI : SealingImpl}.

  Definition interval_client : expr :=
    let: "cap" := intervals () in
    let: "tmp" := "cap" in
    let: "sum" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "max" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "min" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "snap" := Snd "tmp" in
    let: "make_int" := Fst "tmp" in
    let: "i" := "sum" ("make_int" #1 #0) ("make_int" #(-1) #100) in
    assert: ("min" "i" = #-1) ;; assert: ("max" "i" = #101) ;;
    let: "sum_i" := "sum" "i" in
    let: "use" := λ: "j", assert: ("min" "j" ≤ "max" "j") ;; "sum_i" "j" in
    ("use", "cap").

  Definition weak_interval_client : expr :=
    let: "cap" := intervals () in
    let: "tmp" := "cap" in
    let: "sum" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "max" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "min" := Snd "tmp" in let: "tmp" := Fst "tmp" in
    let: "snap" := Snd "tmp" in
    let: "make_int" := Fst "tmp" in
    let: "i" := "sum" ("make_int" #1 #0) ("make_int" #(-1) #100) in
    assert: ("min" "i" = #-1) ;; assert: ("max" "i" = #101) ;;
    let: "sum_i" := "sum" "i" in
    let: "use_weak" := λ: "j",
      let: "j" := "snap" "j" in
      assert: ("min" "j" ≤ "max" "j") ;; "sum_i" "j"
    in
    ("use_weak", "cap").
End interval_client_code.

Section interval_client_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).

  Lemma interval_client_spec N `{!strong_unsealing S} :
    heapN ⊥ N →
    {{{ heap_ctx }}} interval_client {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/interval_client.
    wp_apply (intervals_spec S with "Hh")=>//.
      iIntros (mk snap min max sum γ) "#Hint".
      iDestruct (persistentP with "Hint")
        as "#(Hmk & Hsnap & Hmin & Hmax & Hsum)".
      do 2!wp_let. do 8!(wp_proj; wp_let).
    (** The interval [-1, 101] *)
    wp_apply (make_int_val with "Hmk"). iIntros (i1) "Hi1".
    wp_apply (sum_spec with "[$Hsum $Hi1]"). iIntros (f) "Hf".
    wp_apply (make_int_val with "Hmk"). iIntros (i2) "Hi2".
    wp_apply (sum'_spec with "[$Hf $Hi2]"). iIntros (i) "#Hi". wp_let.
    wp_apply (min_spec with "[$Hmin $Hi]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq.
    wp_apply (max_spec with "[$Hmax $Hi]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq.
    wp_apply (sum_spec with "[$Hsum $Hi]"). iIntros (sum_i) "#Hsum_i".
      do 2!wp_let.
    iApply "HΦ". clear Φ. rewrite low_val. iNext.
    iSplitL; last by iApply (is_intervals_low with "Hint").
    (** The use function is low. *)
    rewrite low_rec. iAlways. iNext. iIntros (v Φ) "_ HΦ". simpl_subst.
    wp_apply (min_any_spec with "Hmin"). iIntros (n1 n2) "Hv".
    wp_apply (max_any_spec with "Hmax"). iIntros (n'1 n'2) "H'v".
    iDestruct (interval_agree with "[$Hv $H'v]") as "[%%]". subst.
    iDestruct (interval_inv with "Hv") as "%".
    wp_apply wp_assert. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext. wp_seq.
    wp_apply (sum'_spec with "[$Hsum_i $Hv]"). iIntros (?) "?".
    iApply "HΦ". by iApply interval_low.
  Qed.

  Lemma weak_interval_client_spec N `{!weak_unsealing S} :
    heapN ⊥ N →
    {{{ heap_ctx }}} weak_interval_client {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/weak_interval_client.
    wp_apply (intervals_spec S with "Hh")=>//.
      iIntros (mk snap min max sum γ) "#Hint".
      iDestruct (persistentP with "Hint")
        as "#(Hmk & Hsnap & Hmin & Hmax & Hsum)".
      do 2!wp_let. do 8!(wp_proj; wp_let).
    (** The interval [-1, 101] *)
    wp_apply (make_int_val with "Hmk"). iIntros (i1) "Hi1".
    wp_apply (sum_spec with "[$Hsum $Hi1]"). iIntros (f) "Hf".
    wp_apply (make_int_val with "Hmk"). iIntros (i2) "Hi2".
    wp_apply (sum'_spec with "[$Hf $Hi2]"). iIntros (i) "#Hi". wp_let.
    wp_apply (min_spec with "[$Hmin $Hi]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq.
    wp_apply (max_spec with "[$Hmax $Hi]"). iIntros "_".
    wp_apply wp_assert. wp_op=>?; last by exfalso. iSplit; first done.
      iNext. wp_seq.
    wp_apply (sum_spec with "[$Hsum $Hi]"). iIntros (sum_i) "#Hsum_i".
      do 2!wp_let.
    iApply "HΦ". clear Φ. rewrite low_val. iNext.
    iSplitL; last by iApply (is_intervals_low with "Hint").
    (** The use_weak function is low (thanks to the snapshot). *)
    rewrite low_rec. iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst.
    wp_apply (snap_low_spec with "[$Hsnap $Hv]"). iIntros (j n1 n2) "#Hj".
      wp_let.
    wp_apply (min_spec with "[$Hmin $Hj]"). iIntros "_".
    wp_apply (max_spec with "[$Hmax $Hj]"). iIntros "_".
      iDestruct (interval_inv with "Hj") as "%".
    wp_apply wp_assert. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext. wp_seq.
    wp_apply (sum'_spec with "[$Hsum_i $Hj]"). iIntros (?) "?".
    iApply "HΦ". by iApply interval_low.
  Qed.
End interval_client_proof.

(** * Public-key interfaces for sealer-unsealer pairs *)
(**
	Morris observed that by keeping a seal function private while
	making the corresponding unseal function public, we obtain
	what amounts to an asymmetric signature scheme and that by
	keeping unseal private while making seal public we obtain an
	asymmetric encryption scheme.

	We formalize Morris' point, proving interfaces for asymmetric
	signature and encryption schemes (with keys buried in
	closures).

	We dispense with the [strong_unsealing] vs [weak_unsealing]
	distinction, baking strong unsealing into our interfaces.
*)
Local Notation ext R := (pointwise_relation _ R).

(** ** Asymmetric signature scheme *)
(**
	Signatures offer no secrecy, so the stipulation in
	[make_sign_spec] that the representation invariant [φ]
	describes low values is entirely reasonable.
*)
Module signing.
Section signing_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) `{!strong_unsealing S}.

  (** Definitions *)

  Definition name := intf.name S.
  Definition is_sign (γ : name) v φ := is_seal S γ v φ.
  Definition is_verify (γ : name) v φ : iProp Σ :=
    (is_unseal S γ v φ ∗ □ (∀ v, φ v -∗ low v))%I.
  Definition is_signed (γ : name) v v' φ := is_sealed S γ v v' φ.

  (** Structure *)

  Global Instance is_sign_persistent γ v φ : PersistentP (is_sign γ v φ).
  Proof. apply _. Qed.
  Global Instance is_sign_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_sign γ v).
  Proof. solve_proper. Qed.

  Global Instance is_verify_persistent γ v φ : PersistentP (is_verify γ v φ).
  Proof. apply _. Qed.
  Global Instance is_verify_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_verify γ v).
  Proof. solve_proper. Qed.

  Global Instance is_signed_persistent γ v v' φ :
    PersistentP (is_signed γ v v' φ).
  Proof. apply _. Qed.
  Global Instance is_signed_ne γ v v' n :
    Proper (ext (dist n) ==> dist n) (is_signed γ v v').
  Proof. solve_proper. Qed.

  (** Properties *)

  Lemma verify_low γ v φ : is_verify γ v φ -∗ low v.
  Proof. iIntros "[Hv Hφ]". by iApply (unseal_low with "Hv Hφ"). Qed.

  Lemma signed_low γ v v' φ : is_signed γ v v' φ -∗ low v'.
  Proof. exact: sealed_low. Qed.

  Lemma signed_inv γ v v' φ : is_signed γ v v' φ -∗ φ v.
  Proof. exact: sealed_inv. Qed.

  Lemma signed_agree γ v1 v2 v' φ :
    is_signed γ v1 v' φ ∗ is_signed γ v2 v' φ ⊢ ⌜v1 = v2⌝.
  Proof. exact: sealed_agree. Qed.

  Lemma make_sign_spec N p φ :
    heapN ⊥ N →
    {{{ heap_ctx ∗ □ (∀ v, φ v -∗ low v) }}} make_seal () @ p; ⊤
    {{{ v1 v2 γ, RET (v1, v2); is_sign γ v1 φ ∗ is_verify γ v2 φ }}}.
  Proof.
    iIntros (? Φ) "[Hh Hφ] HΦ".
    wp_apply (make_seal_spec S N _ φ with "Hh"); first done.
      iIntros (sign verify γ) "[Hs Hv]".
    by iApply ("HΦ" with "[$Hs $Hv $Hφ]").
  Qed.

  Lemma sign_spec p γ sign v φ :
    {{{ is_sign γ sign φ ∗ □ φ v }}} sign v @ p; ⊤
    {{{ v', RET v'; is_signed γ v v' φ }}}.
  Proof. exact: seal_spec. Qed.

  Lemma verify_spec p γ verify v v' φ :
    {{{ is_verify γ verify φ ∗ is_signed γ v v' φ }}} verify v' @ p; ⊤
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "[[Hv _] Hs] HΦ". by iApply (unseal_spec with "[$Hv $Hs]").
  Qed.

  Lemma verify_any_spec γ verify v' φ :
    {{{ is_verify γ verify φ }}} verify v'
    ?{{{ v, RET v; is_signed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[Hv _] HΦ". by iApply (unseal_any_spec with "Hv").
  Qed.
End signing_proof.
Typeclasses Opaque name is_sign is_verify is_signed.
End signing.

(** ** Asymmetric encryption scheme *)
(**
	With malleable encryption, an attacker may transform a
	ciphertext, applying some function to the underlying plaintext
	without learning that plaintext.

	We model malleability in [ctext_inv] which says that the
	plaintext [v] underlying a ciphertext [v'] is either a low
	value (because the adversary encrypted [v]) or a value [f v0]
	for some [v0] satisfying the representation invariant [φ]
	(because the adversary transformed [v0] to [v]).

	Our encryption interface offers (weak) secrecy but no
	integrity; for example, one can encrypt high-integrity
	locations and share the resulting plaintext with an adversary.
*)
Module encryption.
Section encryption_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) `{!strong_unsealing S}.
  Implicit Types v : val.
  Implicit Types f : val → val.

  (** Definitions *)

  Let encφ (φ : val → iProp Σ) : val → iProp Σ :=
    λ v, (low v ∨ ∃ f v0, ⌜v = f v0⌝ ∗ φ v0)%I.

  Definition name := intf.name S.
  Definition is_encrypt (γ : name) v φ := is_seal S γ v (encφ φ).
  Definition is_decrypt (γ : name) v φ := is_unseal S γ v (encφ φ).
  Definition is_ctext (γ : name) v v' φ := is_sealed S γ v v' (encφ φ).

  (** Structure *)

  Lemma encφ_ne n : Proper (ext (dist n) ==> ext (dist n)) encφ.
  Proof. solve_proper. Qed.

  Global Instance is_encrypt_persistent γ v φ :
    PersistentP (is_encrypt γ v φ).
  Proof. apply _. Qed.
  Global Instance is_encrypt_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_encrypt γ v).
  Proof. preprocess_solve_proper. f_equiv. by apply encφ_ne. Qed.
  Global Instance is_encrypt_proper γ v :
    Proper (ext (≡) ==> (≡)) (is_encrypt γ v).
  Proof.
    move=>???. apply equiv_dist=>?. apply is_encrypt_ne=>?.
    by apply equiv_dist.
  Qed.

  Global Instance is_decrypt_persistent γ v φ :
    PersistentP (is_decrypt γ v φ).
  Proof. apply _. Qed.
  Global Instance is_decrypt_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_decrypt γ v).
  Proof. preprocess_solve_proper. f_equiv. by apply encφ_ne. Qed.
  Global Instance is_decrypt_proper γ v :
    Proper (ext (≡) ==> (≡)) (is_decrypt γ v).
  Proof.
    move=>???. apply equiv_dist=>?. apply is_decrypt_ne=>?.
    by apply equiv_dist.
  Qed.

  Global Instance is_ctext_persistent γ v v' φ :
    PersistentP (is_ctext γ v v' φ).
  Proof. apply _. Qed.
  Global Instance is_ctext_ne γ v v' n :
    Proper (ext (dist n) ==> dist n) (is_ctext γ v v').
  Proof. preprocess_solve_proper. f_equiv. by apply encφ_ne. Qed.
  Global Instance is_ctext_proper γ v v' :
    Proper (ext (≡) ==> (≡)) (is_ctext γ v v').
  Proof.
    move=>???. apply equiv_dist=>?. apply is_ctext_ne=>?.
    by apply equiv_dist.
  Qed.

  (** Properties *)

  Lemma encrypt_low γ enc φ : is_encrypt γ enc φ -∗ low enc.
  Proof.
    iIntros "He". iApply (seal_low with "He"). iAlways.
    iIntros (v) "Hv". by iLeft.
  Qed.

  Lemma ctext_low γ v v' φ : is_ctext γ v v' φ -∗ low v'.
  Proof. exact: sealed_low. Qed.

  Lemma ctext_inv γ v v' φ :
    is_ctext γ v v' φ -∗ low v ∨ ∃ f v0, ⌜v = f v0⌝ ∗ φ v0.
  Proof. exact: sealed_inv. Qed.

  Lemma ctext_agree γ v1 v2 v' φ :
    is_ctext γ v1 v' φ ∗ is_ctext γ v2 v' φ ⊢ ⌜v1 = v2⌝.
  Proof. exact: sealed_agree. Qed.

  Lemma make_encrypt_spec N p φ :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_seal () @ p; ⊤
    {{{ v1 v2 γ, RET (v1, v2); is_encrypt γ v1 φ ∗ is_decrypt γ v2 φ }}}.
  Proof. exact: make_seal_spec. Qed.

  Lemma encrypt_spec p γ enc v φ :
    {{{ is_encrypt γ enc φ ∗ □ φ v }}} enc v @ p; ⊤
    {{{ v', RET v'; is_ctext γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[Henc #Hv] HΦ".
    wp_apply (seal_spec with "[$Henc] [$HΦ]").
    iAlways. iRight. iExists id, v. by auto.
  Qed.

  Lemma decrypt_spec p γ dec v v' φ :
    {{{ is_decrypt γ dec φ ∗ is_ctext γ v v' φ }}} dec v' @ p; ⊤
    {{{ RET v; True }}}.
  Proof. exact: unseal_spec. Qed.

  Lemma decrypt_any_spec γ u v' φ :
    {{{ is_decrypt γ u φ }}} u v' ?{{{ v, RET v; is_ctext γ v v' φ }}}.
  Proof. exact: unseal_any_spec. Qed.
End encryption_proof.
Typeclasses Opaque name is_encrypt is_decrypt is_ctext.
End encryption.

(** ** Simple security protocol *)
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
    let: "send" := λ: "x", "sign" ("enc" (ref (assume_even "x"))) in
    let: "recv" := λ: "m", assert_even (! ("dec" ("verify" "m"))) in
    ("send", "recv").
End pk_client.

Section pk_client_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ) `{!strong_unsealing S}
    (N : namespace).
  Implicit Types f v : val.
  Implicit Types n : Z.
  Implicit Types l : loc.
  Import encryption signing.

  Let Nloc : namespace := N .@ "loc".
  Let Nseal : namespace := N .@ "seal".

  Definition plaintext (v : val) : iProp Σ :=
    (∃ l v', ⌜v = l%V⌝ ∗ is_even v' ∗ inv Nloc (l ↦ v'))%I.
  Definition ciphertext (γ : encryption.name S) (v v' : val) : iProp Σ :=
    is_ctext S γ v v' plaintext.
  Definition signature (γ : encryption.name S) (v' : val) : iProp Σ :=
    (∃ v, plaintext v ∗ ciphertext γ v v')%I.

  Lemma plaintext_alloc l v : is_even v -∗ l ↦ v ={⊤}=∗ plaintext l%V.
  Proof.
    iIntros "Hev Hl". iMod (inv_alloc Nloc _ (l ↦ v)%I with "[$Hl]") as "Hinv".
    iModIntro. iExists l, v. by iFrame "Hev Hinv".
  Qed.

  Lemma plaintext_deref p v :
    heapN ⊥ Nloc →
    {{{ heap_ctx ∗ plaintext v }}} ! v @ p; ⊤ {{{ v', RET v'; is_even v' }}}.
  Proof.
    iIntros (? Φ) "[Hh Hv] HΦ". iDestruct "Hv" as (l v') "(% & Hev & Hinv)".
      subst.
    iInv Nloc as "Hl" "Hcl". wp_load. iMod ("Hcl" with "[$Hl]") as "_".
    iApply "HΦ". by iFrame "Hev".
  Qed.

  Lemma signature_low γ v' : signature γ v' -∗ low v'.
  Proof. iDestruct 1 as (v) "[_ Hc]". by iApply ctext_low. Qed.

  Lemma pk_client_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} pk_client {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/pk_client.
    wp_apply (make_encrypt_spec S Nseal _ plaintext with "Hh");
      first by solve_ndisj. iIntros (enc dec γenc) "#[Henc Hdec]".
      wp_let. do 2!(wp_proj; wp_let).
    wp_apply (make_sign_spec S Nseal _ (signature γenc) with "[$Hh]");
      [by solve_ndisj|by iAlways; iIntros; rewrite -signature_low|].
      iIntros (sign ver γsig) "#[Hsign Hver]".
      wp_let. do 2!(wp_proj; wp_let). do 2!wp_let.
    iApply "HΦ". clear Φ. simpl_low. iNext.
    iSplitL; rewrite low_rec; iAlways; iNext; iIntros (v0 Φ) "#Hv0 HΦ";
      simpl_subst.
    (** The send function is low. *)
    - wp_apply assume_even_spec. iIntros "Hev". wp_alloc l as "Hl".
      iMod (plaintext_alloc with "Hev Hl") as "#Hplain".
      wp_apply (encrypt_spec _ _ _ _ l%V with "[$Henc]");
        first by iAlways. iIntros (c) "#Hctext".
      wp_apply (sign_spec with "[$Hsign]").
        { iAlways. iExists l. by iFrame "Hplain Hctext". } iIntros (s) "Hsig".
      iApply "HΦ". by iApply signed_low.
    (** The receive function is low. *)
    - wp_apply (verify_any_spec with "Hver"). iIntros (c) "Hsig".
      iDestruct (signed_inv with "Hsig") as (v) "[Hplain Hctext]".
      wp_apply (decrypt_spec with "[$Hdec $Hctext]"). iIntros "_".
      wp_apply (plaintext_deref with "[$Hh $Hplain]"); first by solve_ndisj.
        iIntros (v') "#Hev".
      (* PDS: generalize assert_even_spec *)
      wp_apply (wp_forget_progress progress).
      wp_apply (assert_even_spec with "Hev"). iIntros "_".
      iApply "HΦ". by iApply is_even_low.
  Qed.
End pk_client_proof.

Section ClosedProofs.
  Import lock.

  Let lock : LockImpl := spin_lock.spin.
  Let sealing : SealingImpl := @direct_sealing.code lock.
  Let interval_client : expr := @interval_client sealing.

  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; sealingΣ; spin_lock.lockΣ ].

  Lemma interval_client_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C interval_client], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.spin_lock. set S := direct_sealing.proof L.
    iApply (interval_client_spec S N with "Hh"); auto with ndisj.
  Qed.

  Let weak_interval_client : expr := @weak_interval_client sealing.
  Lemma weak_interval_client_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C weak_interval_client], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock.spin_lock. set S := direct_sealing.proof L.
    iApply (weak_interval_client_spec S N with "Hh"); auto with ndisj.
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
    set L := spin_lock.spin_lock. set S := direct_sealing.proof L.
    iApply (pk_client_spec S N with "Hh"); auto with ndisj.
  Qed.
End ClosedProofs.

Print Assumptions interval_client_safe.
Print Assumptions weak_interval_client_safe.
Print Assumptions pk_client_safe.
