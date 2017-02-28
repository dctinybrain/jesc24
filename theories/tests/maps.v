From iris.base_logic Require Export big_op.
From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Export constructor.
From iris.heap_lang.lib Require Import abort.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

(** * Finite maps *)
(**
	These are finite maps implemented as association lists, with
	keys built up from any type [K] with a value constructor and
	decidable equality. We don't bother to develop notation and
	functions for lists.
*)
Definition map_empty : val := InjLV ().

Definition map_insert_new: val := λ: "map" "k" "v",
  InjR ("k", "v", "map").

Definition map_lookup : val := rec: "lookup" "map" "k" :=
  match: "map" with
    InjL "x" => assert: "x" = () ;; NONE
  | InjR "cons" =>
    let: "kv" := Fst "cons" in
    if: Fst "kv" = "k" then SOME (Snd "kv") else "lookup" (Snd "cons") "k"
  end.

Definition map_lookup_partial : val := λ: "map" "k",
  match: map_lookup "map" "k" with
    SOME "v" => "v" | NONE => abort
  end.

Section map.
  Context `{heapG Σ} `{EqDecision K, Countable K, fK : constructor K}.
  Implicit Types k : K.
  Implicit Types v : val.

  Fixpoint map_rep (map : val) (kvs : list (K * val)) : Prop :=
    match kvs with
    | [] => map = InjLV ()
    | (k, v) :: kvs => ∃ map', map = InjRV (fK k, v, map') ∧ map_rep map' kvs
    end.

  (**
	The proposition [is_map v m] means that value [v] represents
	the finite partial function [m]. These proofs aren't tricky;
	they amount to boring bookkeeping lemmas.
  *)
  Definition is_map (map : val) (m : gmap K val) : Prop :=
    ∃ kvs, map_rep map kvs ∧ m = map_of_list kvs.

  Lemma map_empty_spec : is_map map_empty ∅.
  Proof. exists []. by simplify_map_eq. Qed.

  Lemma map_insert_new_spec map p E m k v :
    {{{ ⌜is_map map m⌝ ∗ ⌜m !! k = None⌝ }}}
      map_insert_new map (fK k) v @ p; E
    {{{ map', RET map'; ⌜is_map map' (<[k:=v]>m)⌝ }}}.
  Proof.
    iIntros (Φ) "(Hm&%) HΦ". wp_rec. wp_lam. wp_lam.
    iApply "HΦ". iDestruct "Hm" as %(kvs&?&?). iPureIntro.
    subst. exists ((k,v) :: kvs). split.
    by exists map. by rewrite map_of_list_cons.
  Qed.

  Lemma map_lookup_None map p E m k Φ :
    m !! k = None →
    ⌜is_map map m⌝ -∗ ▷ Φ NONEV -∗
    WP map_lookup map (fK k) @ p; E {{ Φ }}.
  Proof.
    iIntros (Hdom) "Hm HΦ".
    iLöb as "IH" forall (map m Hdom). wp_rec. wp_lam.
      iDestruct "Hm" as %(kvs&Hrep&?). subst.
    case: kvs Hrep Hdom=>/=[->|[k' v] kvs [] map' [] -> Hrep] Hdom.
    - wp_match. wp_apply wp_assert. wp_op=>?//.
      iSplit; first done. iNext. by wp_seq.
    wp_finish. wp_match. wp_proj. wp_let. wp_proj. wp_op=>[EQ|NEQ].
    - exfalso. move: EQ Hdom => /(inj fK)->. by simplify_map_eq.
    wp_if. wp_proj.
    wp_apply ("IH" with "[%] [%] [$HΦ]"); last by exists kvs.
    rewrite /= lookup_insert_ne // in Hdom=>?. by subst.
  Qed.

  Lemma map_lookup_Some map p E m k v Φ :
    m !! k = Some v →
    ⌜is_map map m⌝ -∗ ▷ Φ (SOMEV v) -∗
    WP map_lookup map (fK k) @ p; E {{ Φ }}.
  Proof.
    iIntros (Hdom) "Hm HΦ".
    iLöb as "IH" forall (map m Hdom). wp_rec. wp_lam.
      iDestruct "Hm" as %(kvs&Hrep&?). subst.
    case: kvs Hrep Hdom=>/=[->|[k' v'] kvs [] map' [] -> Hrep] Hdom.
    - exfalso. by simplify_map_eq.
    wp_finish. wp_match. wp_proj. wp_let. wp_proj. wp_op=>[EQ|NEQ].
    - wp_if. wp_proj. move: EQ Hdom => /(inj fK)->Hdom.
      simplify_map_eq. iExact "HΦ".
    wp_if. wp_proj.
    wp_apply ("IH" with "[%] [%] [$HΦ]"); last by exists kvs.
    rewrite /= lookup_insert_ne // in Hdom=>?. by subst.
  Qed.

  Lemma map_lookup_spec map p E m k P Φ :
    (m !! k = None → P ⊢ ▷ Φ NONEV) →
    (∀ v, m !! k = Some v → P ⊢ ▷ Φ (SOMEV v)) →
    P ⊢ ⌜is_map map m⌝ -∗ WP map_lookup map (fK k) @ p; E {{ Φ }}.
  Proof.
    iIntros (Hn Hs) "Hp Hm". destruct (m !! k) as [v|] eqn:?.
    - iApply (map_lookup_Some with "Hm"). done. by iApply (Hs with "Hp").
    - iApply (map_lookup_None with "Hm"). done. by iApply (Hn with "Hp").
  Qed.

  Lemma map_lookup_partial_spec map E m k :
    {{{ ⌜is_map map m⌝ }}} map_lookup_partial map (fK k) @ E
    ?{{{ v, RET v; ⌜m !! k = Some v⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ". wp_lam. wp_lam.
    wp_apply (map_lookup_spec _ _ _ _ k with "HΦ Hm").
    - iIntros (?) "? !>". wp_match. by wp_apply wp_abort.
    - iIntros (v ?) "HΦ !>". wp_match. by iApply "HΦ".
  Qed.
End map.
Hint Resolve map_empty_spec.

(** * Partial bijections *)
(**
	These are partial bijections implemented as pairs of finite
	maps. A bijection [f, g : K → K] satisfies [rng f = dom g] and
	[f k1 = k2] implies [g k2 = k1] (with an analogous implication
	in the other direction); that is, [f, g] witness an
	isomorphism.
*)

Definition bij_empty : val := (map_empty, map_empty).

Definition bij_invert : val := λ: "f", (Snd "f", Fst "f").

Definition bij_insert_new : val := λ: "bij" "x" "y",
  let: "f" := map_insert_new (Fst "bij") "x" "y" in
  let: "g" := map_insert_new (Snd "bij") "y" "x" in
  ("f", "g").

Definition bij_lookup : val := λ: "f" "x", map_lookup (Fst "f") "x".

Definition bij_lookup_partial : val := λ: "f" "x",
  map_lookup_partial (Fst "f") "x".

Section bij.
  Context `{heapG Σ} `{EqDecision K, Countable K, fK : constructor K}.
  Implicit Types k : K.
  Implicit Types v : val.

  (**
	The proposition [is_bij v m1 m2] means that value [v]
	represents the partial bijection [m1, m2]. These proofs aren't
	tricky; they amount to boring bookkeeping lemmas.

	TODO: It would be nice to write simply [is_bij v m] with a
	side-conditon [m] a partial bijection.
  *)
  Definition identity (m1 m2 : gmap K val) : Prop :=
    ∀ k1 v2, m1 !! k1 = Some v2 → ∃ k2, v2 = fK k2 ∧ m2 !! k2 = Some (fK k1).

  Definition is_bij (bij : val) (m1 m2 : gmap K val) : Prop :=
    ∃ v1 v2, bij = (v1, v2)%V ∧ is_map v1 m1 ∧ is_map v2 m2 ∧
    identity m1 m2 ∧ identity m2 m1.

  Lemma empty_id : identity ∅ ∅.
  Proof. rewrite/identity. intros. by simplify_map_eq. Qed.
  Hint Resolve empty_id.

  Lemma bij_empty_spec : is_bij bij_empty ∅ ∅.
  Proof. by eexists _, _; auto. Qed.

  Lemma bij_invert_spec p E bij m1 m2 :
    {{{ ⌜is_bij bij m1 m2⌝ }}} bij_invert bij @ p; E
    {{{ bij', RET bij'; ⌜is_bij bij' m2 m1⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ". wp_lam.
      iDestruct "Hm" as (v1 v2) "(Hv&%&%&%&%)".
      iDestruct "Hv" as %->. wp_proj. wp_proj.
    iApply "HΦ". iExists v2, v1. by auto.
  Qed.

  Lemma insert_id k1 k2 m1 m2 :
    identity m1 m2 → m2 !! k2 = None →
    identity (<[k1:=fK k2]> m1) (<[k2:=fK k1]> m2).
  Proof.
    move=>Hid ? k v Hk. case: (decide (k = k1))=>?.
    - subst. exists k2. by simplify_map_eq.
    - simplify_map_eq. move: (Hid _ _ Hk)=>[] k' [] ? Hk'. subst.
      exists k'. by simplify_map_eq.
  Qed.

  Lemma bij_insert_new_spec p E bij k1 k2 m1 m2 :
    {{{ ⌜is_bij bij m1 m2⌝ ∗ ⌜m1 !! k1 = None⌝ ∗ ⌜m2 !! k2 = None⌝ }}}
      bij_insert_new bij (fK k1) (fK k2) @ p; E
    {{{ bij', RET bij'; ⌜is_bij bij' (<[k1:=fK k2]>m1) (<[k2:=fK k1]>m2)⌝ }}}.
  Proof.
    iIntros (Φ) "(Hm & #Hdom1 & #Hdom2) HΦ". wp_lam. wp_let. wp_let.
      iDestruct "Hm" as (v1 v2) "(Hv&Hm1&Hm2&%&%)".
      iDestruct "Hv" as %->. wp_proj.
    wp_apply (map_insert_new_spec with "[$Hm1 $Hdom1]").
      iIntros (v'1) "%". wp_let. wp_proj.
    wp_apply (map_insert_new_spec with "[$Hm2 $Hdom2]").
      iIntros (v'2) "%". wp_let.
    iApply "HΦ". iDestruct "Hdom1" as "%". iDestruct "Hdom2" as "%".
    iPureIntro. eexists _, _. naive_solver auto using insert_id.
  Qed.

  Lemma lookup_id k1 v2 m1 m2 :
    identity m1 m2 → m1 !! k1 = Some v2 → ∃ k2, v2 = fK k2.
  Proof. move=>/(_ k1 v2) Hid /Hid [] k2 [] -> _. by exists k2. Qed.

  Lemma bij_lookup_spec p E bij m1 m2 k1 P Φ :
    (m1 !! k1 = None → P ⊢ ▷ Φ NONEV) →
    (∀ k2, m1 !! k1 = Some (fK k2) → P ⊢ ▷ Φ (SOMEV (fK k2))) →
    P ⊢ ⌜is_bij bij m1 m2⌝ -∗ WP bij_lookup bij (fK k1) @ p; E {{ Φ }}.
  Proof.
    iIntros (? Hfound) "Hp Hm". wp_lam. wp_lam.
      iDestruct "Hm" as (v1 v2) "(Hv&Hm1&_&%&%)".
      iDestruct "Hv" as %[=->]. wp_proj.
    wp_apply (map_lookup_spec with "Hp Hm1"); first done.
    iIntros (v'2 ?) "Hp". destruct (lookup_id k1 v'2 m1 m2) as (k2 & ->)=>//.
    by iApply Hfound.
  Qed.

  Lemma bij_lookup_partial_spec E bij m1 m2 k1 :
    {{{ ⌜is_bij bij m1 m2⌝ }}} bij_lookup_partial bij (fK k1) @ E
    ?{{{ k2, RET fK k2; ⌜m1 !! k1 = Some (fK k2)⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ". wp_lam. wp_lam.
      iDestruct "Hm" as (v1 v2) "(Hv&Hm1&_&%&%)".
      iDestruct "Hv" as %[=->]. wp_proj.
    wp_apply (map_lookup_partial_spec with "Hm1").
    iIntros (v'2) "%". destruct (lookup_id k1 v'2 m1 m2) as (k2 & ->)=>//.
    by iApply "HΦ".
  Qed.
End bij.
