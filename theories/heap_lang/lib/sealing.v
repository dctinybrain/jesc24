From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Import abort lock maps.
From iris.heap_lang Require Import notation proofmode.
Import uPred.

Local Notation ext R := (pointwise_relation _ R).

(* PDS: Missing map ops. *)
Definition map_insert : val := ().
Section map_insert.
  Context `{heapG Σ} `{EqDecision K, Countable K, fK : constructor K}.
  Implicit Types k : K.
  Implicit Types v : val.

  Lemma map_insert_spec map p E m k v :
    {{{ ⌜is_map map m⌝ }}}
      map_insert map (fK k) v @ p; E
    {{{ map', RET map'; ⌜is_map map' (<[k:=v]>m)⌝ }}}.
  Admitted.
End map_insert.

(** * Dynamic sealing interface *)
(**
	Dynamic sealing offers protection analogous to the static
	guarantees obtained with abstract types.

	Our spec lets one pick a representation invariant [φ] when
	allocating a sealer-unsealer pair. The [seal] and [unseal]
	operations then convert between [φ] and [lowval].
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
    (** Predicates. Name separates distinct instances. *)
    name : Type;
    is_sealer_unsealer (N : namespace) (γ : name) (v : val)
      (φ : val → iProp Σ): iProp Σ;
    (** Structure *)
    is_sealer_unsealer_persistent N γ v φ :
      PersistentP (is_sealer_unsealer N γ v φ);
    is_sealer_unsealer_ne N γ v n :
      Proper (ext (dist n) ==> dist n) (is_sealer_unsealer N γ v);
    is_sealer_unsealer_proper N γ v :
      Proper (ext (≡) ==> (≡)) (is_sealer_unsealer N γ v);
    (** Operations *)
    make_sealer_unsealer_spec N p φ `{Hφ : ∀ v, PersistentP (φ v)} :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_sealer_unsealer SI () @ p; ⊤
      {{{ v γ, RET v; is_sealer_unsealer N γ v φ }}};
    seal_spec N p γ s φ `{Hφ : ∀ v, PersistentP (φ v)} :
      {{{ is_sealer_unsealer N γ s φ }}} seal SI s @ p; ⊤ {{{ f, RET f;
        ∀ p v, {{{ φ v }}} f v @ p; ⊤ {{{ v', RET v'; low v' }}}
      }}};
    unseal_spec N p γ s φ :
      {{{ is_sealer_unsealer N γ s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
        ∀ v', {{{ low v' }}} f v' ?{{{ v, RET v; φ v }}}
      }}}
  }.
End spec.
Arguments sealing _ {_ _}.
Existing Instances is_sealer_unsealer_persistent is_sealer_unsealer_ne
  is_sealer_unsealer_proper.

Section lemmas.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).
  Implicit Types v : val.

  Lemma seal_val N p γ s φ v `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_sealer_unsealer S N γ s φ ∗ φ v }}} seal SI s v @ p; ⊤
    {{{ v', RET v'; low v' }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv] HΦ".
    wp_apply (seal_spec with "Hs"). iIntros (f) "Hf".
    wp_apply ("Hf" with "* Hv"). iIntros (v') "Hv'".
    by iApply ("HΦ" with "Hv'").
  Qed.

  Lemma unseal_val N γ s φ v' :
    {{{ is_sealer_unsealer S N γ s φ ∗ low v' }}} unseal SI s v'
    ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "#[Hs Hv'] HΦ".
    wp_apply (unseal_spec with "Hs"). iIntros (f) "Hf".
    by wp_apply ("Hf" with "* Hv'").
  Qed.
End lemmas.
End intf.

(** * Morris' dynamic sealing implementation *)
(**
	Adpated from
<<
		James H. Morris Jr. Protection in Programming
		Languages. CACM 16(1) (January 1973), 15–21.
>>
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
  intf.seal := seal;
  intf.unseal := unseal
|}.
End code.

Module proof.
Section proof.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ) (N : namespace).
  Let SI : SealingImpl := code.sealing LI.
  Implicit Types l : loc.
  Implicit Types f v : val.
  Notation ext R := (pointwise_relation _ R).

  Definition tbl_res (l : loc) (φ : val → iProp Σ) : iProp Σ := (
    ∃ map m, l ↦ map ∗ ⌜is_map (K:=loc) map m⌝ ∗ □ [∗ map] v ∈ m, φ v
  )%I.

  Definition is_sealer_unsealer (l : loc) (v : val) (φ : val → iProp Σ) : iProp Σ := (
    ∃ sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜v = (sync, l)%V⌝ ∗
    is_sync sync (tbl_res l φ)
  )%I.

  Global Instance is_sealer_unsealer_persistent l v φ :
    PersistentP (is_sealer_unsealer l v φ).
  Proof. apply _. Qed.

  Instance tbl_res_ne l n : Proper (ext (dist n) ==> dist n) (tbl_res l).
  Proof. solve_proper. Qed.

  Global Instance is_sealer_unsealer_ne l v n :
    Proper (ext (dist n) ==> dist n) (is_sealer_unsealer l v).
  Proof. solve_proper. Qed.

  Instance tbl_res_proper l : Proper (ext (≡) ==> (≡)) (tbl_res l).
  Proof. solve_proper. Qed.

  Global Instance is_sealer_unsealer_proper l v :
    Proper (ext (≡) ==> (≡)) (is_sealer_unsealer l v).
  Proof. solve_proper. Qed.

  Lemma make_sealer_unsealer_spec p φ `{Hφ : ∀ v, PersistentP (φ v)} :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_sealer_unsealer SI () @ p; ⊤
    {{{ v l, RET v; is_sealer_unsealer l v φ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc l as "Hl". wp_let.
    wp_apply (make_sync_spec L _ N (tbl_res l φ) with "[$Hh Hl]")=>//.
    { iExists map_empty, ∅. iFrame "Hl". iSplitL.
      - iPureIntro. exact: map_empty_spec.
      - iAlways. by rewrite big_sepM_empty. }
    iIntros (sync) "Hsync". wp_let.
    iApply "HΦ". iExists sync. by iFrame "% Hh Hsync".
  Qed.

  Lemma seal_spec p l s φ `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_sealer_unsealer l s φ }}} seal SI s @ p; ⊤ {{{ f, RET f;
      ∀ p v, {{{ φ v }}} f v @ p; ⊤ {{{ v', RET v'; low v' }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (vk Φ) "_ HΦ". simpl_subst.
      iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst.
      do 2!(wp_proj; wp_let).
    wp_typecast Hloc; wp_match; last by wp_apply wp_abort.
      destruct (is_loc_val _ Hloc) as (k&->). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & Hm & #Hrng)". wp_load.
    (* PDS: Hack. *)
      iDestruct (map_insert_spec map noprogress ⊤ m k v with "Hm") as "Hins".
      rewrite /map_insert.
    wp_apply "Hins". iIntros (map') "Hm'". wp_store.
    iApply ("HΨ" with "[Hl Hm']"); last by iApply "HΦ"; simpl_low.
    iExists map', (<[k:=v]> m). iFrame "Hl Hm'". iAlways.
    case Hv': (m !! k) => [v'|].
    - rewrite (big_sepM_insert_override_2 _ _ _ v' v) //.
      iApply "Hrng". by iIntros.
    - rewrite big_sepM_insert //. by iFrame "Hv Hrng".
  Qed.

  Lemma unseal_spec p l s φ :
    {{{ is_sealer_unsealer l s φ }}} unseal SI s @ p; ⊤ {{{ f, RET f;
      ∀ v', {{{ low v' }}} f v' ?{{{ v, RET v; φ v }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (v') "!#". iIntros (Φ) "#Hv' HΦ". wp_lam.
      iDestruct "Hs" as (sync) "(%&#Hh&%&Hsync)". subst.
      do 2!(wp_proj; wp_let).
    wp_apply (wp_alloc_low with "[$Hh]"); auto; first by simpl_low.
      iIntros (k) "Hk". wp_let.
    (* PDS: Hack. *)
    (*
	[wp_on_val_app] should be a Texan triple.
	And, once we simplify robust safety, there's no call for
	stating those lemmas in terms of expression.
    *)
    wp_bind (v' k). iDestruct (wp_on_val_app lowloc v' k) as "Happ".
      rewrite (wp_wand _ _ (v' k)%E _ _).
    wp_apply ("Happ" with "[Hv'] [Hk]");
      [by rewrite low_val_eq|by rewrite low_loc on_val_elim|].
    iIntros (?) "_". wp_seq. iClear "Happ".
    (* PDS: End hack. *)
    rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & % & #Hrng)". wp_load.
    wp_apply (map_lookup_partial_spec _ _  _ k with "[%]")=>//.
      iIntros (v'') "%".
    iApply ("HΨ" with "[Hl]").
    - iExists map, m. iFrame "% Hl". iAlways. by iFrame "Hrng".
    - iApply "HΦ". by rewrite -(big_sepM_lookup (λ k v, φ v) m k v'').
  Qed.
End proof.

Definition sealing `{heapG Σ, LockImpl} (L : lock Σ) : sealing Σ := {|
  intf.make_sealer_unsealer_spec := make_sealer_unsealer_spec L;
  intf.seal_spec := seal_spec;
  intf.unseal_spec := unseal_spec
|}.
End proof.
