From iris.algebra Require Import auth gmap agree.
From iris.heap_lang Require Import addenda.
From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Import abort lock maps.
From iris.heap_lang Require Import notation proofmode.
Import addenda.option.
Import uPred.

Local Notation ext R := (pointwise_relation _ R).

(** * Dynamic sealing interface *)
(**
	Morris introduced dynamic sealing in
<<
	James H. Morris Jr. Protection in Programming Languages.
	CACM 16(1) (January 1973), 15–21.
>>
	His idea was to associate dynamic "type tags" with values
	satisfying a representation invariant in order to approximate
	the convenience of working in a language with abstract types
	(while interoperating with untrusted, potentially ill-typed
	code).

	Our spec lets one pick a representation invariant [φ] when
	allocating a sealer-unsealer pair. The [seal] and [unseal]
	operations then convert between [φ] and [lowval]. There are
	two triples for [unseal]. The progressive triple returns a
	predictable value, and is suitable for use in verified code.
	The non-progressive triple returns *some* value.
*)
Module Import intf.

(** Operations *)
Class SealingImpl : Set := {
  make_sealer_unsealer : val; seal : val; unseal : val
}.
Arguments make_sealer_unsealer _ : clear implicits.
Arguments seal _ : clear implicits.
Arguments unseal _ : clear implicits.

Section spec.
  Context `{heapG Σ} {SI : SealingImpl}.
  Implicit Types v f : val.

  Structure sealing := Sealing {
    (** Predicates. *)
    (** Name ties [is_sealer_unsealer] to [is_sealed]. *)
    name : Type;
    is_sealer_unsealer (N : namespace) (γ : name) (v : val)
      (φ : val → iProp Σ) : iProp Σ;
    is_sealed (N : namespace) (γ : name) (v v' : val) : iProp Σ;
    (** Structure *)
    is_sealer_unsealer_persistent N γ v φ :
      PersistentP (is_sealer_unsealer N γ v φ);
    is_sealer_unsealer_ne N γ v n :
      Proper (ext (dist n) ==> dist n) (is_sealer_unsealer N γ v);
    is_sealed_persistent N γ v v' :
      PersistentP (is_sealed N γ v v');
    (** Operations *)
    make_sealer_unsealer_spec N p φ `{Hφ : ∀ v, PersistentP (φ v)} :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_sealer_unsealer SI () @ p; ⊤
      {{{ v γ, RET v; is_sealer_unsealer N γ v φ }}};
    seal_spec N p γ s φ `{Hφ : ∀ v, PersistentP (φ v)} :
      {{{ is_sealer_unsealer N γ s φ }}} seal SI s @ p; ⊤ {{{ f, RET f; ∀ p v,
        {{{ φ v }}} f v @ p; ⊤ {{{ v', RET v'; low v' ∗ is_sealed N γ v v' }}}
      }}};
    unseal_sealed_spec N p γ s φ :
      {{{ is_sealer_unsealer N γ s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
        ∀ p v v', {{{ is_sealed N γ v v' }}} f v' @ p; ⊤ {{{ RET v; φ v }}}
      }}};
    unseal_low_spec N p γ s φ :
      {{{ is_sealer_unsealer N γ s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
        ∀ v', {{{ low v' }}} f v' ?{{{ v, RET v; φ v }}}
      }}}
  }.
End spec.
Arguments sealing _ {_ _}.
Existing Instances is_sealer_unsealer_persistent is_sealer_unsealer_ne
  is_sealed_persistent.

Section lemmas.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).
  Implicit Types v : val.

  Global Instance is_sealer_unsealer_proper N γ v :
    Proper (ext (≡) ==> (≡)) (is_sealer_unsealer S N γ v).
  Proof.
    move=>???. apply equiv_dist=>?. apply is_sealer_unsealer_ne=>?.
    by apply equiv_dist.
  Qed.

  Lemma seal_val N p γ s φ v `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_sealer_unsealer S N γ s φ ∗ φ v }}} seal SI s v @ p; ⊤
    {{{ v', RET v'; low v' ∗ is_sealed S N γ v v' }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv] HΦ".
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
    wp_apply ("Hf" with "* Hv"). iIntros (v') "Hv'".
    by iApply ("HΦ" with "Hv'").
  Qed.

  Lemma unseal_sealed_val N p γ s φ v v' :
    {{{ is_sealer_unsealer S N γ s φ ∗ is_sealed S N γ v v' }}}
      unseal SI s v' @ p; ⊤
    {{{ RET v; φ v }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ".
    wp_apply (unseal_sealed_spec with "Hs"). iIntros (f) "Hf".
    by wp_apply ("Hf" with "* Hv'").
  Qed.

  Lemma unseal_low_val N γ s φ v' :
    {{{ is_sealer_unsealer S N γ s φ ∗ low v' }}} unseal SI s v'
    ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ".
    wp_apply (unseal_low_spec with "Hs"). iIntros (f) "Hf".
    by wp_apply ("Hf" with "* Hv'").
  Qed.
End lemmas.
End intf.

(** * Morris' dynamic sealing implementation *)
(**
	Safe-for-space implementations exist. The sequential code
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

Module code.
Section code.
  Context (LI : LockImpl).

  Definition make_sealer_unsealer : val := λ: <>,
    let: "tbl" := ref map_empty in
    let: "sync" := make_sync LI () in
    ("sync", "tbl").

  Definition seal : val := λ: "p" "v" "x",
    let: "sync" := Fst "p" in let: "tbl" := Snd "p" in
    ifloc: "x" as "k" => "sync" (λ: <>, "tbl" <- map_insert (! "tbl") "k" "v")
    else abort.

  Definition unseal : val := λ: "p" "f",
    let: "sync" := Fst "p" in let: "tbl" := Snd "p" in
    let: "k" := ref () in
    "f" "k" ;;
    "sync" (λ: <>, map_lookup_partial (! "tbl") "k").
End code.

Definition sealing (LI : LockImpl) : SealingImpl := {|
  intf.make_sealer_unsealer := make_sealer_unsealer LI;
  intf.seal := seal; intf.unseal := unseal
|}.
End code.

Module proof.
(** The CMRA we need. *)
Notation heap := (gmap loc val).
Definition heapUR : ucmraT := gmapUR loc (agreeR valC).
Class sealingG Σ := SealingG { sealing_heapG :> inG Σ (authR heapUR) }.

Definition sealingΣ : gFunctors := #[ GFunctor (constRF (authR heapUR)) ].
Instance subG_sealingΣ {Σ} : subG sealingΣ Σ → sealingG Σ.
Proof. intros [??]%subG_inv. constructor; apply _. Qed.

Section proof.
  Context `{heapG Σ, sealingG Σ, LI : LockImpl} (L : lock Σ) (N : namespace).
  Let SI : SealingImpl := code.sealing LI.
  Implicit Types l : loc.
  Implicit Types f v : val.
  Notation ext R := (pointwise_relation _ R).

  Let name : Type := gname * loc.

  (**
	The assertion [is_witness γ k v] represents knowledge that the
	table underlying the sealer-unsealer pair named [γ] sends
	location [k] to value [v].
  *)
  Definition is_witness (γ : name) (k : loc) (v : val) : iProp Σ :=
    own (γ.1) (◯ {[k := to_agree v]}).

  (**
	The table underlying the sealer-unsealer pair named [γ] sends
	locations [k] to values satisfying the representation
	invariant [φ]. Moreover, locations [k] arising from verified
	applications of [unseal] are tied to a ghost heap witnessing
	the table's assignment of a particular value [v] to [k].

	The table can bind locations not tracked by the ghost heap
	because adversarial code can apply a sealed value to a
	low-integrity value [kv]. When [kv] is a location [k], such
	applications extend the table (but not the ghost heap).

	We store actual heap resources alongside the ghost heap to
	ensure we can allocate [is_witness γ k v] given a fresh, high
	location [k].
  *)
  Definition to_heap : heap → heapUR := fmap to_agree.

  Definition witness (γ : name) (m : heap) : iProp Σ := (
    ∃ h, ⌜h ⊆ m⌝ ∗ own (γ.1) (● to_heap h) ∗ live (dom _ h) ∗
    [∗ map] k↦_ ∈ h, k ↦ ()
  )%I.

  Definition tbl_res (γ : name) (φ : val → iProp Σ) : iProp Σ := (
    ∃ map m, (γ.2) ↦ map ∗ is_map map m ∗ witness γ m ∗
    [∗ map] v ∈ m, □ φ v
  )%I.

  Definition is_sealer_unsealer (γ : name) (v : val) φ : iProp Σ := (
    ∃ sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜v = (sync, γ.2)%V⌝ ∗
    is_sync sync (tbl_res γ φ)
  )%I.

  (*
	The assertion [is_sealed γ v v'] represents knowledge that
	value [v'] was obtained by sealing value [v] with the
	sealer-unsealer pair named [γ].

	Unfolding the definition, we have a progressive triple for [v'
	k] that converts a high, fresh location [k] to a witness
	[is_witness γ k v] sufficient to ensure that table lookups on
	[k] will compute [v]
  *)
  Definition is_sealed (γ : name) (v v' : val) : iProp Σ := (
    ∀ p k,
    {{{ k ↦ () ∗ fresh k }}} v' k @ p; ⊤ {{{ RET (); is_witness γ k v }}}
  )%I.

  (** Structure *)

  Instance is_witness_persistent γ k v : PersistentP (is_witness γ k v).
  Proof. apply _. Qed.
  Instance is_witness_timeless γ k v : TimelessP (is_witness γ k v).
  Proof. apply _. Qed.

  Instance tbl_res_ne γ n : Proper (ext (dist n) ==> dist n) (tbl_res γ).
  Proof. solve_proper. Qed.

  Global Instance is_sealer_unsealer_persistent γ v φ :
    PersistentP (is_sealer_unsealer γ v φ).
  Proof. apply _. Qed.
  Global Instance is_sealer_unsealer_ne γ v n :
    Proper (ext (dist n) ==> dist n) (is_sealer_unsealer γ v).
  Proof.
    (* FIXME: [solve_proper] works but is very slow here *)
    move=>φ1 φ2 Hφ. preprocess_solve_proper.
    apply exist_ne. do 4!f_equiv. apply is_sync_ne. f_equiv. by apply Hφ.
  Qed.

  Global Instance is_sealed_persistent γ v v' : PersistentP (is_sealed γ v v').
  Proof. apply _. Qed.

  (** Ghosts *)

  Lemma witness_elim γ m k v :
    witness γ m -∗ is_witness γ k v -∗ ⌜m !! k = Some v⌝.
  Proof.
    iIntros "Hw Hk". iDestruct "Hw" as (h) "(%&Hγ&_)".
    iDestruct (own_valid_2 with "Hγ Hk") as %[Hinc _]%auth_valid_discrete_2.
    iPureIntro. apply (map_subseteq_spec h m); first done.
    move: Hinc. rewrite singleton_included lookup_fmap=>-[] u [].
    case: (h !! k)=>[vh|]/=; last by move=>/option_equivE.
    move=>Heq. apply (inj Some) in Heq. unfold_leibniz. rewrite -Heq.
    by case/Some_included=>[/(inj to_agree) | /to_agree_included]->.
  Qed.

  Lemma witness_high_alloc γ h k v :
    h !! k = None →
    own (γ.1) (● to_heap h) ==∗
    own (γ.1) (● to_heap (<[k:=v]> h)) ∗ is_witness γ k v.
  Proof.
    rewrite /to_heap fmap_insert -own_op=>Hdom.
    apply own_update, auth_update_alloc, alloc_singleton_local_update.
    by rewrite lookup_fmap Hdom. done.
  Qed.

  Lemma witness_high γ m k v :
    heap_ctx -∗ witness γ m -∗ k ↦ () -∗ fresh k ={⊤}=∗
    witness γ (<[k:=v]> m) ∗ is_witness γ k v.
  Proof.
    iIntros "#Hh Hw Hk Hf". iDestruct "Hw" as (h) "(%&Hγ&Hlive&Hhigh)".
    iMod (heap_mark_live with "Hh Hf Hlive") as "(Hdom&Hlive)"; first done.
      iDestruct "Hdom" as %?%not_elem_of_dom.
    iMod (witness_high_alloc _ _ k v with "Hγ") as "[Hγ Hw]"; first done.
    iModIntro. iFrame "Hw". iExists (<[k:=v]> h). iFrame "Hγ".
    rewrite dom_insert_L. iFrame "Hlive".
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

  Lemma witness_low γ m k v :
    witness γ m -∗ low k -∗ witness γ (<[k:=v]> m).
  Proof.
    iIntros "Hw Hk". iDestruct "Hw" as (h) "(%&Hγ&Hlive&Hhigh)". iExists h.
    iDestruct (witness_low_sep with "Hhigh Hk") as "#Hdom".
      iDestruct "Hdom" as %Hdom.
    iFrame "Hγ Hlive Hhigh". iPureIntro. apply map_subseteq_spec=>x vx.
    case: (decide (k = x))=>[<-|?]; first by rewrite Hdom.
    rewrite lookup_insert_ne //. by apply map_subseteq_spec.
  Qed.

  Lemma tbl_inv_insert (m : heap) k v (φ : val → iProp Σ)
      `{Hv : ∀ v, PersistentP (φ v)} :
    ([∗ map] v ∈ m, □ φ v) -∗ φ v -∗ [∗ map] v ∈ <[k:=v]> m, □ φ v.
  Proof.
    iIntros "Hinv #Hv". case Hv': (m !! k) => [v'|].
    - rewrite (big_sepM_insert_override_2 _ _ _ v' v) //.
      iApply "Hinv". iIntros "_". iAlways. by iFrame "Hv".
    - rewrite big_sepM_insert //. iFrame "Hinv". iAlways. by iFrame "Hv".
  Qed.

  (** Operations *)

(* PDS: We probably do not need heapN ⊥ N after allocation. *)
  Lemma make_sealer_unsealer_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_sealer_unsealer SI () @ p; ⊤
    {{{ v γ, RET v; is_sealer_unsealer γ v φ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc l as "Hl". wp_let.
      rewrite -wp_fupd. set h := to_heap ∅.
    iMod (own_alloc (Auth (Excl' h) h)) as (γh) "Hγh"; first done.
      rewrite (auth_both_op h). iDestruct "Hγh" as "[Hγh _]".
      set γ : name := (γh, l).
    iAssert (witness γ ∅) with "[Hγh]" as "Hw".
    { iExists ∅. iFrame "Hγh".
      rewrite dom_empty_L big_sepS_empty big_sepM_empty. by auto. }
    wp_apply (make_sync_spec L _ N (tbl_res γ φ) with "[$Hh Hl Hw]");
      first done.
    { iExists map_empty, ∅. iFrame "Hl Hw". rewrite big_sepM_empty. by auto. }
    iIntros (sync) "Hsync". wp_let.
    iApply ("HΦ" $! _ γ). iExists sync. by iFrame "% Hh Hsync".
  Qed.

  Lemma seal_spec p γ s φ `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_sealer_unsealer γ s φ }}} seal SI s @ p; ⊤ {{{ f, RET f; ∀ p v,
      {{{ φ v }}} f v @ p; ⊤ {{{ v', RET v'; low v' ∗ is_sealed γ v v' }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
    iApply "HΦ". clear Φ. iSplitL.

    (** The seal is a low function. *)
    - rewrite low_rec. iAlways. iNext. iIntros (vk Φ) "#Hk HΦ". simpl_subst.
        iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst.
        do 2!(wp_proj; wp_let).
      wp_typecast Hloc; wp_match; last by wp_apply wp_abort.
        destruct (is_loc_val _ Hloc) as (k&->). rewrite/is_sync.
      wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
        iDestruct "HR" as (map m) "(Hl & Hm & Hw & #Hinv)". wp_load.
      wp_apply (map_insert_spec _ _ _ m with "Hm").
        iIntros (map') "Hm'". wp_store.
      iApply ("HΨ" with "[Hl Hm' Hw]"); last by iApply "HΦ"; simpl_low.
      iExists map', (<[k:=v]> m). iFrame "Hl Hm'". iSplitL.
      + rewrite (low_val k). by iApply (witness_low with "Hw Hk").
      + by iApply (tbl_inv_insert with "Hinv Hv").

    (** The seal satisfies [is_sealed]. *)
    - clear p. iIntros (p k) "!#". iIntros (Φ) "[Hk Hf] HΦ". wp_lam.
        iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst.
        do 2!(wp_proj; wp_let).
      wp_typecast Hloc; last by exfalso; apply Hloc; exists k.
        wp_match. rewrite/is_sync.
      wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
        iDestruct "HR" as (map m) "(Hl & Hm & Hw & #Hinv)". wp_load.
      wp_apply (map_insert_spec _ _ _ m with "Hm").
        iIntros (map') "Hm'". rewrite -wp_fupd. wp_store.
      iMod (witness_high _ _ k v with "Hh Hw Hk Hf") as "[Hw Hkv]".
      iApply ("HΨ" with "[Hl Hm' Hw]"); last by iApply ("HΦ" with "Hkv").
      iExists map', (<[k:=v]> m). iFrame "Hl Hm' Hw".
      by iApply (tbl_inv_insert with "Hinv Hv").
  Qed.

  Lemma unseal_sealed_spec p γ s φ :
    {{{ is_sealer_unsealer γ s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
      ∀ p v v', {{{ is_sealed γ v v' }}} f v' @ p; ⊤ {{{ RET v; φ v }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p v v') "!#". iIntros (Φ) "#Hv' HΦ".
      wp_lam. iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst.
      do 2!(wp_proj; wp_let).
    wp_apply (wp_alloc_fresh with "Hh"); auto.
      iIntros (k) "[Hk Hf]". wp_let. rewrite/is_sealed.
    wp_apply ("Hv'" with "* [$Hk $Hf]"). iIntros "Hkv". wp_seq. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      iDestruct (witness_elim with "Hw Hkv") as "%".
    wp_apply (map_lookup_partial_Some_spec _ _ _ _ k with "Hm");
      first done. iIntros "_".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. by iFrame "Hl Hm Hw Hinv".
    - iApply "HΦ". setoid_rewrite always_elim.
      by iApply (big_sepM_lookup (λ _, φ) m k v with "Hinv").
  Qed.

  Lemma unseal_low_spec p γ s φ :
    {{{ is_sealer_unsealer γ s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
      ∀ v', {{{ low v' }}} f v' ?{{{ v, RET v; φ v }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (v') "!#". iIntros (Φ) "#Hv' HΦ". wp_lam.
      iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst. do 2!(wp_proj; wp_let).
    wp_apply (wp_alloc_low with "[$Hh]"); auto; first by simpl_low.
      iIntros (k) "Hk". wp_let.
(*
	PDS: Hack. [wp_on_val_app] should be a Texan triple and
	there's no call to state those lemmas in terms of expressions.
*)
    wp_bind (v' k). iDestruct (wp_on_val_app lowloc v' k) as "Happ".
      rewrite (wp_wand _ _ (v' k)%E _ _).
    wp_apply ("Happ" with "[Hv'] [Hk]");
      [by rewrite low_val_eq|by rewrite low_loc on_val_elim|].
    iIntros (?) "_". wp_seq. iClear "Happ".
(* PDS: End hack. *)
    rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
    wp_apply (map_lookup_partial_spec _ _  _ k with "Hm")=>//.
      iIntros (v'') "%".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. by iFrame "Hl Hm Hw Hinv".
    - iApply "HΦ". setoid_rewrite always_elim.
      by rewrite -(big_sepM_lookup (λ _, φ) m k v'').
  Qed.
End proof.

Definition sealing `{heapG Σ, sealingG Σ, LockImpl}
    (L : lock Σ) : sealing Σ := {|
  intf.make_sealer_unsealer_spec := make_sealer_unsealer_spec L;
  intf.seal_spec := seal_spec;
  intf.unseal_sealed_spec := unseal_sealed_spec;
  intf.unseal_low_spec := unseal_low_spec
|}.
End proof.
