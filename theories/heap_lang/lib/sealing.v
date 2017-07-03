From iris.algebra Require Import auth gmap agree.
From iris.heap_lang Require Import addenda.
From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Import abort lock maps.
From iris.heap_lang Require Import notation proofmode.
Import addenda.option addenda.algebra_auth.
Import uPred.

Local Notation ext R := (pointwise_relation _ R).

(** * Dynamic sealing interface *)
(**
	Morris introduced dynamic sealing in
<<
	James H. Morris Jr. Protection in Programming Languages.
	CACM 16(1) (January 1973), 15–21.
>>
	His idea was to dynamically approximate the convenience of
	working in a language with abstract types while interoperating
	with untrusted, potentially ill-typed code.

	Our spec lets one pick a representation invariant [φ] when
	allocating a sealer-unsealer pair. The [seal] and [unseal]
	operations then convert between [φ] and [lowval]. There are
	two triples for [unseal]. The progressive triple returns a
	predictable value, and is suitable for proving functional
	correctness properties. The non-progressive triple returns
	*some* value satisfying [φ].

	Morris' implementation of sealing satisfies this
	specification. A simpler, more direct implementation of
	sealing satisfies a stronger specification whereby unsealing
	an arbitrary value [v'] produces a value [v] that had
	previously been sealed.
*)
Module Import intf.

(** Operations *)
Class SealingImpl : Set := { make_seal : val }.

Section spec.
  Context `{heapG Σ} {SI : SealingImpl}.
  Implicit Types v f : val.

  Structure sealing := Sealing {
    (** Predicates. *)
    (** Name ties together the abstract predicates. *)
    name : Type;
    is_seal (γ : name) (v : val) (φ : val → iProp Σ) : iProp Σ;
    is_unseal (γ : name) (v : val) (φ : val → iProp Σ) : iProp Σ;
    is_sealed (γ : name) (v v' : val) (φ : val → iProp Σ) : iProp Σ;
    (** Structure *)
    is_seal_persistent γ v φ : PersistentP (is_seal γ v φ);
    is_seal_ne γ v n : Proper (ext (dist n) ==> dist n) (is_seal γ v);
    is_unseal_persistent γ v φ : PersistentP (is_unseal γ v φ);
    is_unseal_ne γ v n : Proper (ext (dist n) ==> dist n) (is_unseal γ v);
    is_sealed_persistent γ v v' φ : PersistentP (is_sealed γ v v' φ);
    is_sealed_ne γ v v' n : Proper (ext (dist n) ==> dist n) (is_sealed γ v v');
    (** Low seal, unseal, and sealed values *)
    seal_low γ s φ : is_seal γ s φ -∗ □ (∀ v, low v -∗ φ v) -∗ low s;
    unseal_low γ u φ : is_unseal γ u φ -∗ □ (∀ v, φ v -∗ low v) -∗ low u;
    sealed_low γ v v' φ : is_sealed γ v v' φ -∗ low v';
    sealed_inv γ v v' φ : is_sealed γ v v' φ -∗ φ v;
    sealed_agree γ v1 v2 v' φ :
      is_sealed γ v1 v' φ ∗ is_sealed γ v2 v' φ ⊢ ⌜v1 = v2⌝;
    (** Operations *)
    make_seal_spec N p φ :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_seal () @ p; ⊤
      {{{ v1 v2 γ, RET (v1, v2); is_seal γ v1 φ ∗ is_unseal γ v2 φ }}};
    seal_spec p γ s v φ :
      {{{ is_seal γ s φ ∗ □ φ v }}} s v @ p; ⊤
      {{{ v', RET v'; is_sealed γ v v' φ }}};
    unseal_spec p γ u v v' φ :
      {{{ is_unseal γ u φ ∗ is_sealed γ v v' φ }}} u v' @ p; ⊤
      {{{ RET v; True }}}
  }.
  Class weak_unsealing (S : sealing) : Prop :=
    unseal_low_spec γ u v' φ :
      {{{ is_unseal S γ u φ ∗ low v' }}} u v' ?{{{ v, RET v; φ v }}}.
  Class strong_unsealing (S : sealing) : Prop :=
    unseal_any_spec γ u v' φ :
      {{{ is_unseal S γ u φ }}} u v' ?{{{ v, RET v; is_sealed S γ v v' φ }}}.
End spec.
Arguments sealing _ {_ _}.
Existing Instances is_seal_persistent is_seal_ne
  is_unseal_persistent is_unseal_ne
  is_sealed_persistent is_sealed_ne.

Section instances.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).

  Global Instance is_seal_proper γ v : Proper (ext (≡) ==> (≡)) (is_seal S γ v).
  Proof.
    move=>???. apply equiv_dist=>?. apply is_seal_ne=>?.
    by apply equiv_dist.
  Qed.

  Global Instance is_unseal_proper γ v :
    Proper (ext (≡) ==> (≡)) (is_unseal S γ v).
  Proof.
    move=>???. apply equiv_dist=>?. apply is_unseal_ne=>?.
    by apply equiv_dist.
  Qed.

  Global Instance is_sealed_proper γ v v' :
    Proper (ext (≡) ==> (≡)) (is_sealed S γ v v').
  Proof.
    move=>???. apply equiv_dist=>?. apply is_sealed_ne=>?.
    by apply equiv_dist.
  Qed.

  Global Instance weaken_unsealing `{!strong_unsealing S} :
    weak_unsealing S.
  Proof.
    iIntros (γ u v' φ Φ) "[Hu _] HΦ".
    wp_apply (unseal_any_spec with "Hu"). iIntros (?) "?".
    iApply "HΦ". by iApply sealed_inv.
  Qed.
End instances.
End intf.

(** * Witness heaps *)
(**
	Both of the following proofs rely on a so-called _witness
	heap_; that is, a ghost heap [h] sending locations [k] to
	sealed values [v].
*)
(** The CMRA we need. *)
Local Notation heap := (gmap loc val).
Definition heapUR : ucmraT := gmapUR loc (agreeR valC).
Class sealingG Σ := SealingG { sealing_heapG :> inG Σ (authR heapUR) }.

Definition sealingΣ : gFunctors := #[ GFunctor (constRF (authR heapUR)) ].
Instance subG_sealingΣ {Σ} : subG sealingΣ Σ → sealingG Σ.
Proof. intros [??]%subG_inv. constructor; apply _. Qed.

Module witness.
Section witness.
  Context `{heapG Σ, sealingG Σ}.

  (** Definitions. *)

  (**
	The assertion [is_witness γ k v] represents knowledge that the
	witness heap named [γ] sends location [k] to value [v].
  *)
  Definition is_witness (γ : gname) (k : loc) (v : val) : iProp Σ :=
    own γ (◯ {[k := to_agree v]}).
  Definition to_heap : heap → heapUR := fmap to_agree.
  Definition witness (γ : gname) (h : heap) : iProp Σ :=
    (own γ (● to_heap h) ∗ live (dom _ h))%I.

  (** Structure *)

  Global Instance is_witness_persistent γ k v :
    PersistentP (is_witness γ k v).
  Proof. apply _. Qed.
  Global Instance is_witness_timeless γ k v :
    TimelessP (is_witness γ k v).
  Proof. apply _. Qed.

  (** Ghosts *)

  Lemma witness_alloc : (|==> ∃ γ, witness γ ∅)%I.
  Proof.
    set h := to_heap ∅.
    iMod (own_alloc (Auth (Excl' h) h)) as (γ) "Hw"; first done.
    iModIntro. iExists γ.
    rewrite (auth_both_op h). iDestruct "Hw" as "[Hw _]". iFrame "Hw".
    by rewrite dom_empty_L big_sepS_empty.
  Qed.

  Lemma is_witness_elim γ h k v :
    witness γ h -∗ is_witness γ k v -∗ ⌜h !! k = Some v⌝.
  Proof.
    iIntros "[Hw _] Hk".
    iDestruct (own_valid_2 with "Hw Hk") as %[Hinc _]%auth_valid_discrete_2.
    iPureIntro.
    move: Hinc. rewrite singleton_included lookup_fmap=>-[] u [].
    case: (h !! k)=>[vh|]/=; last by move=>/option_equivE.
    move=>Heq. apply (inj Some) in Heq. unfold_leibniz. rewrite -Heq.
    by case/Some_included=>[/(inj to_agree) | /to_agree_included]->.
  Qed.

  Lemma is_witness_alloc' γ h k v :
    h !! k = None →
    own γ (● to_heap h) ==∗
    own γ (● to_heap (<[k:=v]> h)) ∗ is_witness γ k v.
  Proof.
    rewrite /to_heap fmap_insert -own_op=>Hdom.
    apply own_update, auth_update_alloc, alloc_singleton_local_update.
    by rewrite lookup_fmap Hdom. done.
  Qed.

  Lemma is_witness_alloc γ h k v :
    heap_ctx -∗ witness γ h -∗ fresh k ={⊤}=∗
    ⌜h !! k = None⌝ ∗ witness γ (<[k:=v]> h) ∗ is_witness γ k v.
  Proof.
    iIntros "#Hh [Hw Hlive] Hk".
    iMod (heap_mark_live with "Hh Hk Hlive") as "(Hdom&Hlive)"; first done.
      iDestruct "Hdom" as %?%not_elem_of_dom.
    iMod (is_witness_alloc' _ _ k v with "Hw") as "[Hw Hv]"; first done.
    iModIntro. iFrame "% Hw Hv". rewrite dom_insert_L. by iFrame "Hlive".
  Qed.

  Lemma witness_obs γ h k v :
    h !! k = Some v →
    witness γ h ==∗ witness γ h ∗ is_witness γ k v.
  Proof.
    iIntros (Hdom) "[Hw HL]". rewrite/witness/is_witness. iFrame "HL".
    rewrite -own_op. iApply (own_update with "Hw").
    apply auth_frag_alloc; try apply _. apply singleton_included.
    exists (to_agree v). split. by rewrite lookup_fmap Hdom. done.
  Qed.

  Lemma is_witness_agree γ k v1 v2 :
    is_witness γ k v1 ∗ is_witness γ k v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite -own_op -auth_frag_op.
    rewrite own_valid auth_validI /= discrete_valid.
    rewrite op_singleton singleton_valid.
    by f_equiv=>/agree_op_inv/to_agree_inj/leibniz_equiv_iff.
  Qed.

  (** Somewhat orthogonal. *)
  Lemma tbl_inv_insert (h : heap) k v (φ : loc → val → iProp Σ) :
    ([∗ map] k↦v ∈ h, φ k v) -∗ φ k v -∗
    [∗ map] k↦v ∈ <[k:=v]> h, φ k v.
  Proof.
    iIntros "Hinv Hk". case Hv': (h !! k) => [v'|].
    - rewrite (big_sepM_insert_override_2 _ _ _ v' v) //.
      iApply "Hinv". iIntros "_". by iFrame "Hk".
    - rewrite big_sepM_insert //. by iFrame "Hinv Hk".
  Qed.
End witness.
End witness.

(** * Morris' sealing implementation *)
(**
	Other than the typecast, this is a transliteration of Morris'
	code. We need the typecast to match our library for finite
	maps which assumes a type of values with decidable equality
	(here, locations).

	Safe-for-space implementations likely exist. We conjecture
	that the sequential code
<<
	let r = ref None in
	let seal x = λ _, r := Some x in
	let unseal f = (r := None; f (); valOf (! r)) in
	(seal, unseal)
>>
	could be adpated to the concurrent setting (e.g., using
	reentrant locks).

	Attribution: This sequential implementation isn't new. It is
	based on E language code at
<<
	http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns#Sealers_and_Unsealers
>>
	(accessed in February 2017).
*)
Module morris_sealing.
Import witness.

Section code.
  Context {LI : LockImpl}.

  Definition make_seal : val := λ: <>,
    let: "tbl" := ref map_empty in
    let: "sync" := make_sync () in
    let: "seal" := λ: "v" "x",
      ifloc: "x" as "k" =>
        "sync" (λ: <>, "tbl" <- map_insert (! "tbl") "k" "v")
      else abort
    in
    let: "unseal" := λ: "f",
      let: "k" := ref () in
      "f" "k" ;;
      "sync" (λ: <>, map_lookup_partial (! "tbl") "k")
    in
    ("seal", "unseal").

  Global Instance code : SealingImpl := {|
    intf.make_seal := make_seal
  |}.
End code.

Section proof.
  Context `{heapG Σ, sealingG Σ, LI : LockImpl} (L : lock Σ).
  Implicit Types l : loc.
  Implicit Types f v : val.

  (**
	The table underlying the sealer-unsealer pair named [γ] sends
	locations [k] to values satisfying the representation
	invariant [φ]. Moreover, locations [k] arising from verified
	applications of [unseal] are tied to a witness heap.
	(Witnesses are used to prove the progressive triple for
	unsealing.)

	The table must account for locations not tracked by the
	witness heap because adversarial code can apply a sealed value
	to a low-integrity value [kv]. When [kv] is a location [k],
	such applications extend the table, but not the witness heap.

	The resource [witness_some γ m] ties the witness heap to a
	sealer-unsealer pair with table contents [m] and to heap
	resources that ensure we can allocate witnesses given a fresh,
	high location [k].
  *)

  Definition witness_some (γ : gname) (m : heap) : iProp Σ := (
    ∃ h, ⌜h ⊆ m⌝ ∗ witness γ h ∗ [∗ map] k↦_ ∈ h, k ↦ ()
  )%I.

  Definition tbl_res (l : loc) (γ : gname) (φ : val → iProp Σ) : iProp Σ := (
    ∃ map m, l ↦ map ∗ is_map map m ∗ witness_some γ m ∗
    □ [∗ map] v ∈ m, φ v
  )%I.

  Record name : Type := { sync : val; tbl : loc; ghost : gname }.
  Definition ctx (γ : name) φ : iProp Σ :=
    (heap_ctx ∗ is_sync (sync γ) (tbl_res (tbl γ) (ghost γ) φ))%I.

  Definition is_seal γ v φ : iProp Σ := (
    ctx γ φ ∗
    ⌜v = LamV "v" (λ: "x",
      ifloc: "x" as "k" =>
        (sync γ) (λ: <>, tbl γ <- map_insert (! (tbl γ)) "k" "v")
      else abort)⌝
  )%I.

  Definition is_unseal γ v φ : iProp Σ := (
    ctx γ φ ∗
    ⌜v = LamV "f" (
      let: "k" := ref () in
      "f" "k" ;;
      (sync γ) (λ: <>, map_lookup_partial (! (tbl γ)) "k"))⌝
  )%I.

  Definition is_sealed γ v v' φ : iProp Σ := (
    ctx γ φ ∗ □ φ v ∗
    ⌜v' = LamV "x" (
      ifloc: "x" as "k" =>
        (sync γ) (λ: <>, tbl γ <- map_insert (! (tbl γ)) "k" v)
      else abort)%E⌝
  )%I.

  (** Structure *)

  Instance tbl_res_ne l γ n : Proper (ext (dist n) ==> dist n) (tbl_res l γ).
  Proof. solve_proper. Qed.

  Instance ctx_persistent γ φ : PersistentP (ctx γ φ).
  Proof. apply _. Qed.
  Instance ctx_ne γ n : Proper (ext (dist n) ==> dist n) (ctx γ).
  Proof. solve_proper. Qed.

  Instance is_seal_persistent γ v φ : PersistentP (is_seal γ v φ).
  Proof. apply _. Qed.
  Instance is_seal_ne γ v n : Proper (ext (dist n) ==> dist n) (is_seal γ v).
  Proof. solve_proper. Qed.

  Instance is_unseal_persistent γ v φ : PersistentP (is_unseal γ v φ).
  Proof. apply _. Qed.
  Instance is_unseal_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_unseal γ v).
  Proof. solve_proper. Qed.

  Instance is_sealed_persistent γ v v' φ : PersistentP (is_sealed γ v v' φ).
  Proof. apply _. Qed.
  Instance is_sealed_ne γ v v' n :
    Proper (ext (dist n) ==> dist n) (is_sealed γ v v').
  Proof. solve_proper. Qed.

  (** Ghosts *)

  Lemma witness_some_alloc : (|==> ∃ γ, witness_some γ ∅)%I.
  Proof.
    iMod witness_alloc as (γ) "Hw". iModIntro. iExists γ, ∅. iFrame "Hw".
    rewrite big_sepM_empty. by auto.
  Qed.

  Lemma is_witness_some_elim γ m k v :
    witness_some γ m -∗ is_witness γ k v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hw Hk". iDestruct "Hw" as (h) "(%&Hw&_)".
    iDestruct (is_witness_elim with "Hw Hk") as "%". iPureIntro.
    by apply (map_subseteq_spec h m).
  Qed.

  Lemma is_witness_alloc_high γ m k v :
    heap_ctx -∗ witness_some γ m -∗ k ↦ () -∗ fresh k ={⊤}=∗
    witness_some γ (<[k:=v]> m) ∗ is_witness γ k v.
  Proof.
    iIntros "#Hh Hw Hk Hf". iDestruct "Hw" as (h) "(%&Hw&Hhigh)".
    iMod (is_witness_alloc _ _ _ v with "Hh Hw Hf") as "(%&Hw&Hv)".
    iModIntro. iFrame "Hv". iExists (<[k:=v]> h). iFrame "Hw".
    rewrite big_sepM_insert //. iFrame "Hk Hhigh".
    iPureIntro. apply map_subseteq_spec=>x vx.
    case: (decide (k = x))=>[<-|?]; first by rewrite !lookup_insert.
    do 2!rewrite lookup_insert_ne //. by apply (map_subseteq_spec h m).
  Qed.

  Lemma witness_low_sep (h : heap) k :
    ([∗ map] k↦_ ∈ h, k ↦ ()) -∗ low k -∗ ⌜h !! k = None⌝.
  Proof.
    induction h as [|x vx h Hx IH] using map_ind; iIntros "Hhigh Hl";
      first by rewrite lookup_empty.
    rewrite big_sepM_insert //. iDestruct "Hhigh" as "[Hh Hhigh]".
    case: (decide (k = x))=>?.
    - iExFalso. subst. by iApply (high_not_low with "[$Hh $Hl]").
    - rewrite lookup_insert_ne //. by iApply (IH with "Hhigh Hl").
  Qed.

  Lemma witness_some_low γ m k v :
    witness_some γ m -∗ low k -∗ witness_some γ (<[k:=v]> m).
  Proof.
    iIntros "Hw Hk". iDestruct "Hw" as (h) "(%&Hγ&Hhigh)". iExists h.
    iDestruct (witness_low_sep with "Hhigh Hk") as "#Hdom".
      iDestruct "Hdom" as %Hdom.
    iFrame "Hγ Hhigh". iPureIntro. apply map_subseteq_spec=>x vx.
    case: (decide (k = x))=>[<-|?]; first by rewrite Hdom.
    rewrite lookup_insert_ne //. by apply map_subseteq_spec.
  Qed.

  (** Operations *)

  Lemma make_seal_spec N p φ :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_seal () @ p; ⊤
    {{{ v1 v2 γ, RET (v1, v2); is_seal γ v1 φ ∗ is_unseal γ v2 φ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc l as "Hl". wp_let.
      rewrite -wp_fupd.
    iMod witness_some_alloc as (γh) "Hw".
    wp_apply (make_sync_spec L _ N (tbl_res l γh φ) with "[$Hh Hl Hw]");
      first done.
    { iExists map_empty, ∅. iFrame "Hl Hw".
      rewrite big_sepM_empty. iSplitL. by auto. by iAlways. }
    iIntros (sync) "#Hsync". iCombine "Hh" "Hsync" as "Hctx".
      set γ := {| sync := sync; tbl := l; ghost := γh |}. do 3!wp_let.
    iApply ("HΦ" $! _ _ γ). iFrame "Hctx Hctx". by auto.
  Qed.

  (** Properties of sealing *)

  Lemma seal_spec p γ s v φ :
    {{{ is_seal γ s φ ∗ □ φ v }}} s v @ p; ⊤
    {{{ v', RET v'; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] #Hv] HΦ". subst. wp_lam.
    iApply "HΦ". iFrame "Hctx". iSplitL. by iAlways. done.
  Qed.

  Lemma sealed_inv γ v v' φ : is_sealed γ v v' φ -∗ φ v.
  Proof. iIntros "(_ &#Hv&_)". by iFrame "Hv". Qed.

  Lemma sealed_agree γ v1 v2 v' φ :
    is_sealed γ v1 v' φ ∗ is_sealed γ v2 v' φ ⊢ ⌜v1 = v2⌝.
  Proof. iIntros "[(_&_&%) (_&_&%)]". by naive_solver. Qed.

  Lemma sealed_low γ v v' φ : is_sealed γ v v' φ -∗ low v'.
  Proof.
    iIntros "(#[Hh Hsync] & #Hv & %)". subst. rewrite low_rec.
      iAlways. iNext. iIntros (vk Φ) "#Hk HΦ". simpl_subst.
    wp_typecast Hloc; wp_match; last by wp_apply wp_abort.
      destruct (is_loc_val _ Hloc) as (k&->). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & Hm & Hw & #Hinv)". wp_load.
    wp_apply (map_insert_spec _ _ _ m with "Hm").
      iIntros (map') "Hm'". wp_store.
    iApply ("HΨ" with "[Hl Hm' Hw]"); last by iApply "HΦ"; simpl_low.
    iExists map', (<[k:=v]> m). iFrame "Hl Hm'". iSplitL.
    - rewrite (low_val k). by iApply (witness_some_low with "Hw Hk").
    - iAlways. by iApply (tbl_inv_insert with "Hinv [Hv]").
  Qed.

  Lemma seal_low γ s φ : is_seal γ s φ -∗ □ (∀ v, low v -∗ φ v) -∗ low s.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst. wp_value.
    iApply "HΦ".
    iApply (sealed_low γ v with "[]"). iFrame "Hctx".
    iSplitL; last done. iAlways. by iApply ("Hφ" with "Hv").
  Qed.

  Lemma sealed_high p γ v v' k φ :
    {{{ is_sealed γ v v' φ ∗ k ↦ () ∗ fresh k }}} v' k @ p; ⊤
    {{{ RET (); is_witness (ghost γ) k v }}}.
  Proof.
    iIntros (Φ) "((#[Hh Hsync] & #Hv & %) & Hk & Hf) HΦ". subst. wp_lam.
    wp_typecast Hloc; last by exfalso; apply Hloc; exists k.
      wp_match. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & Hm & Hw & #Hinv)". wp_load.
    wp_apply (map_insert_spec _ _ _ m with "Hm").
      iIntros (map') "Hm'". rewrite -wp_fupd. wp_store.
    iMod (is_witness_alloc_high _ _ k v with "Hh Hw Hk Hf") as "[Hw Hkv]".
    iApply ("HΨ" with "[Hv Hl Hm' Hw]"); last by iApply ("HΦ" with "Hkv").
    iExists map', (<[k:=v]> m). iFrame "Hl Hm' Hw". iAlways.
    by iApply (tbl_inv_insert with "Hinv Hv").
  Qed.

  (** Properties of unsealing. *)

  Lemma unseal_spec p γ u v v' φ :
    {{{ is_unseal γ u φ ∗ is_sealed γ v v' φ }}} u v' @ p; ⊤
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "[[#[Hh Hsync] %] Hv'] HΦ". subst. wp_lam.
    wp_apply (wp_alloc_fresh with "Hh"); auto.
      iIntros (k) "[Hk Hf]". wp_let.
    wp_apply (sealed_high with "[$Hv' $Hk $Hf]"). iIntros "Hwk". wp_seq.
      rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      iDestruct (is_witness_some_elim with "Hw Hwk") as "%".
    wp_apply (map_lookup_partial_Some_spec _ _ _ _ k with "Hm");
      first done. iIntros "_".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. iFrame "Hl Hm Hw". by iAlways.
    - by iApply "HΦ".
  Qed.

  Lemma unseal_body_low γ v' φ :
    {{{ ctx γ φ ∗ low v' }}}
      let: "k" := ref () in
      v' "k" ;;
      (sync γ) (λ: <>, (map_lookup_partial ! (tbl γ)) "k")
    ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "(#[Hh Hsync] & #Hv') HΦ".
    wp_apply (wp_alloc_low with "[$Hh]"); auto; first by simpl_low.
      iIntros (k) "Hk". wp_let. wp_bind (v' k).
    wp_apply (wp_on_val_app _ _ k with "[$Hv' Hk]");
      first by rewrite low_loc; simpl_on_val. iIntros (?) "_".
      wp_seq. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
    wp_apply (map_lookup_partial_spec _ _  _ k with "Hm")=>//.
      iIntros (v'') "%".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. iFrame "Hl Hm Hw". by iAlways.
    - iApply "HΦ". by rewrite -(big_sepM_lookup (λ _, φ) m k v'').
  Qed.

  Lemma unseal_low γ u φ :
    is_unseal γ u φ -∗ □ (∀ v, φ v -∗ low v) -∗ low u.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v' Φ) "#Hv' HΦ". simpl_subst.
    wp_apply (unseal_body_low with "[$Hctx $Hv']"). iIntros (v) "Hv".
    iApply "HΦ". by iApply ("Hφ" with "Hv").
  Qed.

  Lemma unseal_low_spec γ u v' φ :
    {{{ is_unseal γ u φ ∗ low v' }}} u v' ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (unseal_body_low with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Definition proof : sealing Σ := {|
    intf.seal_low := seal_low;
    intf.unseal_low := unseal_low;
    intf.sealed_low := sealed_low;
    intf.sealed_inv := sealed_inv;
    intf.sealed_agree := sealed_agree;
    intf.make_seal_spec := make_seal_spec;
    intf.seal_spec := seal_spec;
    intf.unseal_spec := unseal_spec
  |}.
  Global Instance weak : weak_unsealing proof := unseal_low_spec.
End proof.
End morris_sealing.

(** * Direct implementation *)
(**
	In contrast to Morris' implementation of sealing, this
	implemenation supports [strong_unsealing] because low
	locations are less tricky than low functions.

	With Morris' implementation of sealing, for example, an
	adversary with values [f1, f2] obtained by sealing values [v1,
	v2] can construct a function
<<
	let r = ref false in
	λ k,
	let b := !r in
	r := (not b);
	(if b then f1 else f2) k
>>
	that, when unsealed, oscillates between [v1] and [v2].
*)
Module direct_sealing.
Import witness.

Section code.
  Context {LI : LockImpl}.

  Definition make_seal : val := λ: <>,
    let: "tbl" := ref map_empty in
    let: "sync" := make_sync () in
    let: "seal" := λ: "v",
      let: "k" := ref () in
      "sync" (λ: <>, "tbl" <- map_insert_new (! "tbl") "k" "v") ;;
      "k"
    in
    let: "unseal" := λ: "x",
      ifloc: "x" as "k" =>
        "sync" (λ: <>, map_lookup_partial (! "tbl") "k")
      else abort
    in
    ("seal", "unseal").

  Global Instance code : SealingImpl := {|
    intf.make_seal := make_seal
  |}.
End code.

Section proof.
  Context `{heapG Σ, sealingG Σ, LI : LockImpl} (L : lock Σ).
  Implicit Types l k : loc.
  Implicit Types f v : val.

  Definition tbl_res (l : loc) (γ : gname) (φ : val → iProp Σ) : iProp Σ := (
    ∃ map m, l ↦ map ∗ is_map map m ∗ witness γ m ∗
    □ [∗ map] k ↦ v ∈ m, low k ∗ φ v
  )%I.

  Record name : Type := { sync : val; tbl : loc; ghost : gname }.

  Definition ctx (γ : name) φ : iProp Σ :=
    (heap_ctx ∗ is_sync (sync γ) (tbl_res (tbl γ) (ghost γ) φ))%I.

  Definition is_seal γ v φ : iProp Σ := (
    ctx γ φ ∗
    ⌜v = LamV "v" (
      let: "k" := ref () in
      (sync γ) (λ: <>, (tbl γ) <- map_insert_new (! (tbl γ)) "k" "v") ;;
      "k")⌝
  )%I.

  Definition is_unseal γ v φ : iProp Σ := (
    ctx γ φ ∗
    ⌜v = LamV "x" (
      ifloc: "x" as "k" =>
        (sync γ) (λ: <>, map_lookup_partial (! (tbl γ)) "k")
      else abort)%E⌝
  )%I.

  Definition is_sealed γ v v' φ : iProp Σ :=
    (ctx γ φ ∗ □ φ v ∗ low v' ∗ ∃ k, ⌜v' = k⌝ ∗ is_witness (ghost γ) k v)%I.

  (** Structure *)

  Instance tbl_res_ne l γ n : Proper (ext (dist n) ==> dist n) (tbl_res l γ).
  Proof. solve_proper. Qed.

  Instance ctx_persistent γ φ : PersistentP (ctx γ φ).
  Proof. apply _. Qed.
  Instance ctx_ne γ n : Proper (ext (dist n) ==> dist n) (ctx γ).
  Proof. solve_proper. Qed.

  Instance is_seal_persistent γ v φ : PersistentP (is_seal γ v φ).
  Proof. apply _. Qed.
  Instance is_seal_ne γ v n : Proper (ext (dist n) ==> dist n) (is_seal γ v).
  Proof. solve_proper. Qed.

  Instance is_unseal_persistent γ v φ : PersistentP (is_unseal γ v φ).
  Proof. apply _. Qed.
  Instance is_unseal_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_unseal γ v).
  Proof. solve_proper. Qed.

  Instance is_sealed_persistent γ v v' φ : PersistentP (is_sealed γ v v' φ).
  Proof. apply _. Qed.
  Instance is_sealed_ne γ v v' n :
    Proper (ext (dist n) ==> dist n) (is_sealed γ v v').
  Proof. solve_proper. Qed.

  (** Operations *)

  Lemma make_seal_spec N p φ :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_seal () @ p; ⊤
    {{{ v1 v2 γ, RET (v1, v2); is_seal γ v1 φ ∗ is_unseal γ v2 φ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc l as "Hl". wp_let.
      rewrite -wp_fupd.
    iMod witness_alloc as (γh) "Hw".
    wp_apply (make_sync_spec L _ N (tbl_res l γh φ) with "[$Hh Hl Hw]");
      first done.
    { iExists map_empty, ∅. iFrame "Hl Hw". rewrite big_sepM_empty.
      iSplitL. by auto. by iAlways. }
    iIntros (sync) "#Hsync". iCombine "Hh" "Hsync" as "Hctx".
      set γ := {| sync := sync; tbl := l; ghost := γh |}. do 3!wp_let.
    iApply ("HΦ" $! _ _ γ). iFrame "Hctx Hctx". by auto.
  Qed.

  (** Properties of sealing *)

  Lemma sealed_inv γ v v' φ : is_sealed γ v v' φ -∗ φ v.
  Proof. by iIntros "(_ &#?&_&_)". Qed.

  Lemma sealed_low γ v v' φ : is_sealed γ v v' φ -∗ low v'.
  Proof. by iIntros "(_ &_&#?&_)". Qed.

  Lemma sealed_agree γ v1 v2 v' φ :
    is_sealed γ v1 v' φ ∗ is_sealed γ v2 v' φ ⊢ ⌜v1 = v2⌝.
  Proof.
    iIntros "[(_&_&_&Hv1) (_&_&_&Hv2)]".
    iDestruct "Hv1" as (k1) "[% Hk1]". subst.
    iDestruct "Hv2" as (k2) "[EQ Hk2]". iDestruct "EQ" as %[=<-].
    by iApply (is_witness_agree with "[$Hk1 $Hk2]").
  Qed.

  Lemma seal_body p γ v φ :
    {{{ ctx γ φ ∗ □ φ v }}}
      let: "k" := ref () in
      (sync γ) (λ: <>, tbl γ <- ((map_insert_new ! (tbl γ)) "k") v) ;; "k"
    @ p; ⊤ {{{ v', RET v'; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "#[[Hh Hsync] Hv] HΦ".
    wp_apply (wp_alloc_low_fresh with "[$Hh]")=>//; first by simpl_low.
      iIntros (k) "[#Hklow Hkfresh]". wp_let. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      rewrite -fupd_wp.
    iMod (is_witness_alloc _ _ k v with "Hh Hw Hkfresh") as "(%&Hw&Hkv)".
      iModIntro.
    wp_apply (map_insert_new_spec _ _ _ m with "[$Hm]"); first done.
      iIntros (map') "Hm'". wp_store.
    iApply ("HΨ" with "[Hl Hm' Hw]").
    - iExists map', (<[k:=v]> m). iFrame "Hl Hm' Hw".
      iCombine "Hklow" "Hv" as "Hk". rewrite (always_elim (φ v)).
      by iApply (tbl_inv_insert with "Hinv Hk").
    - wp_seq. iApply "HΦ". iFrame "Hh Hv".
      rewrite/is_sync; iFrame "Hsync".
      simpl_low. iFrame "Hklow". iExists k. by iFrame "Hkv".
  Qed.

  Lemma seal_low γ s φ : is_seal γ s φ -∗ □ (∀ v, low v -∗ φ v) -∗ low s.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst.
    wp_apply (seal_body with "[$Hctx Hφ Hv]").
    - iAlways. by iApply ("Hφ" with "Hv").
    - iIntros (v') "Hv'". iApply "HΦ". by iApply (sealed_low with "Hv'").
  Qed.

  Lemma seal_spec p γ s v φ :
    {{{ is_seal γ s φ ∗ □ φ v }}} s v @ p; ⊤
    {{{ v', RET v'; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] #Hv] HΦ". subst. wp_lam.
    wp_apply (seal_body with "[$Hctx Hv] [$HΦ]"). by iAlways.
  Qed.

  (** Properties of unsealing. *)

 Lemma unseal_spec p γ u v v' φ :
    {{{ is_unseal γ u φ ∗ is_sealed γ v v' φ }}} u v' @ p; ⊤
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "[[#[Hh Hsync] %] Hv'] HΦ". subst. wp_lam.
      iDestruct "Hv'" as "(_&#Hv&#Hv'&Hw)". iDestruct "Hw" as (k) "[% #Hk]".
      subst.
    wp_typecast Hloc; last by exfalso; apply: Hloc; exists k. wp_match.
      rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      iDestruct (is_witness_elim with "Hw Hk") as "%".
    wp_apply (map_lookup_partial_Some_spec _ _ _ _ k with "Hm")=>//.
      iIntros "_".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. iFrame "Hl Hm Hw". by iAlways.
    - by iApply "HΦ".
  Qed.

  Lemma unseal_body_any γ v' φ :
    {{{ ctx γ φ }}}
      ifloc: v' as "k" => (sync γ) (λ: <>, map_lookup_partial (! (tbl γ)) "k")
      else abort
    ?{{{ v, RET v; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "#[Hh Hsync] HΦ".
    wp_typecast Hloc; wp_match; last by wp_apply wp_abort.
      destruct (is_loc_val _ Hloc) as (k&->). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      rewrite -wp_fupd.
    wp_apply (map_lookup_partial_spec _ _  _ k with "Hm")=>//.
      iIntros (v'') "%".
    iMod (witness_obs with "Hw") as "[Hw Hk]"; first done.
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. iFrame "Hl Hm Hw". by iAlways.
    - iApply "HΦ". iFrame "Hh". rewrite /is_sync; iFrame "Hsync".
      rewrite assoc. iSplitR; last by iExists k; auto.
      iDestruct (big_sepM_lookup _ _ k v'' with "Hinv") as "[Hk Hv'']";
        first done.
      simpl_low. iFrame "Hk". by iAlways.
  Qed.

  Lemma unseal_low γ u φ :
    is_unseal γ u φ -∗ □ (∀ v, φ v -∗ low v) -∗ low u.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v' Φ) "#Hv' HΦ". simpl_subst.
    wp_apply (unseal_body_any with "Hctx").
      iIntros (v) "Hv".
    iApply "HΦ". iApply "Hφ". by iApply (sealed_inv with "Hv").
  Qed.

  Lemma unseal_any_spec γ u v' φ :
    {{{ is_unseal γ u φ }}} u v' ?{{{ v, RET v; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[Hctx %] HΦ". subst. wp_lam.
    by wp_apply (unseal_body_any with "Hctx [$HΦ]").
  Qed.

  Definition proof : sealing Σ := {|
    intf.seal_low := seal_low;
    intf.unseal_low := unseal_low;
    intf.sealed_low := sealed_low;
    intf.sealed_inv := sealed_inv;
    intf.sealed_agree := sealed_agree;
    intf.make_seal_spec := make_seal_spec;
    intf.seal_spec := seal_spec;
    intf.unseal_spec := unseal_spec
  |}.
  Global Instance strong : strong_unsealing proof := unseal_any_spec.
End proof.
End direct_sealing.
