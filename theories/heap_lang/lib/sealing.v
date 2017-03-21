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
    (** Operations *)
    make_seal_spec N p φ :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_seal () @ p; ⊤
      {{{ v1 v2 γ, RET (v1, v2); is_seal γ v1 φ ∗ is_unseal γ v2 φ }}};
    seal_spec p γ s v φ `{!PersistentP (φ v)} :
      {{{ is_seal γ s φ ∗ φ v }}} s v @ p; ⊤
      {{{ v', RET v'; is_sealed γ v v' φ }}};
    unseal_spec p γ u v v' φ :
      {{{ is_unseal γ u φ ∗ is_sealed γ v v' φ }}} u v' @ p; ⊤
      {{{ RET v; φ v }}};
    unseal_low_spec γ u v' φ :
      {{{ is_unseal γ u φ ∗ low v' }}} u v' ?{{{ v, RET v; φ v }}}
  }.
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
End instances.

(** * The reseal operation *)
(**
	Unsealing a low value [f] twice need not return the _same_ value
	[v] because an adversary with access to two sealed values [v'1]
	and [v'2] may define
<<
	f ≔ let r = ref true in λ _, if !r then (r := false; v'1) else v'2
>>
	The application [reseal f] applies [f] once and returns a
	more predictable sealed value [f'].
*)
Definition reseal : val := λ: "seal" "unseal" "x", "seal" ("unseal" "x").

Section reseal_proof.
  Context `{heapG Σ, SI : SealingImpl} (S : sealing Σ).
  Implicit Types s u f v : val.

  Lemma reseal_spec p γ s φ `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_seal S γ s φ }}} reseal s @ p; ⊤ {{{ f1, RET f1;
      ∀ p u, {{{ is_unseal S γ u φ }}} f1 u @ p; ⊤ {{{ f2, RET f2;
        ∀ v', {{{ low v' }}} f2 v' ?{{{ v'2 v, RET v'2; is_sealed S γ v v'2 φ }}}
      }}}
    }}}.
  Proof.
    iIntros (Φ) "#Hs HΦ". wp_lam.
    iApply "HΦ". clear p Φ. iIntros (p u) "!#". iIntros (Φ) "#Hu HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (v') "!#". iIntros (Φ) "Hv' HΦ". wp_lam.
    wp_apply (unseal_low_spec with "[$Hu $Hv']"). iIntros (v) "Hv".
    wp_apply (seal_spec with "[$Hs $Hv]"). iIntros (v'2) "Hv'2".
    by iApply ("HΦ" with "Hv'2").
  Qed.

  Lemma reseal_val γ s u v' φ `{Hφ : ∀ v, PersistentP (φ v)} :
    {{{ is_seal S γ s φ ∗ is_unseal S γ u φ ∗ low v' }}} reseal s u v'
    ?{{{  v'2 v, RET v'2; is_sealed S γ v v'2 φ }}}.
  Proof.
    iIntros (Φ) "(Hs & Hu & Hv') HΦ".
    wp_apply (reseal_spec with "Hs"). iIntros (f1) "Hf1".
    wp_apply ("Hf1" with "* Hu"). iIntros (f2) "Hf2".
    by wp_apply ("Hf2" with "* Hv'").
  Qed.
End reseal_code.

End intf.

(** * Dynamic sealing implementation *)
(**
	Other than the typecast, this is a transliteration of Morris'
	implementation of sealing.

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
  Context {LI : LockImpl}.

  Definition make_seal : val := λ: <>,
    let: "tbl" := ref map_empty in
    let: "sync" := make_sync LI () in
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

  Global Instance sealing : SealingImpl := {|
    intf.make_seal := make_seal
  |}.
End code.
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
  Context `{heapG Σ, sealingG Σ, LI : LockImpl} (L : lock Σ).
  Implicit Types l : loc.
  Implicit Types f v : val.
  Notation ext R := (pointwise_relation _ R).

  (**
	The table underlying the sealer-unsealer pair named [γ] sends
	locations [k] to values satisfying the representation
	invariant [φ]. Moreover, locations [k] arising from verified
	applications of [unseal] are tied to a ghost heap witnessing
	the table's assignment of a particular value [v] to [k].

	The table must account for locations not tracked by the ghost
	heap because adversarial code can apply a sealed value to a
	low-integrity value [kv]. When [kv] is a location [k], such
	applications extend the table, but not the ghost heap.

	The assertion [is_witness γ k v] represents knowledge that the
	ghost heap sends location [k] to value [v] and is used to
	prove the progressive triple for unsealing. The resource
	[witness γ m] ties the ghost heap to a sealer-unsealer pair
	with table contents [m] and heap resources that ensure we can
	allocate [is_witness γ k v] given a fresh, high location [k].
  *)

  Definition is_witness (γ : gname) (k : loc) (v : val) : iProp Σ :=
    own γ (◯ {[k := to_agree v]}).

  Definition to_heap : heap → heapUR := fmap to_agree.
  Definition witness (γ : gname) (m : heap) : iProp Σ := (
    ∃ h, ⌜h ⊆ m⌝ ∗ own γ (● to_heap h) ∗ live (dom _ h) ∗
    [∗ map] k↦_ ∈ h, k ↦ ()
  )%I.

  Definition tbl_res (l : loc) (γ : gname) (φ : val → iProp Σ) : iProp Σ := (
    ∃ map m, l ↦ map ∗ is_map map m ∗ witness γ m ∗
    [∗ map] v ∈ m, □ φ v
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

  Instance is_witness_persistent γ k v : PersistentP (is_witness γ k v).
  Proof. apply _. Qed.
  Instance is_witness_timeless γ k v : TimelessP (is_witness γ k v).
  Proof. apply _. Qed.

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
    own γ (● to_heap h) ==∗
    own γ (● to_heap (<[k:=v]> h)) ∗ is_witness γ k v.
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

  Lemma tbl_inv_insert (m : heap) k v (φ : val → iProp Σ) :
    ([∗ map] v ∈ m, □ φ v) -∗ □ φ v -∗ [∗ map] v ∈ <[k:=v]> m, □ φ v.
  Proof.
    iIntros "Hinv #Hv". case Hv': (m !! k) => [v'|].
    - rewrite (big_sepM_insert_override_2 _ _ _ v' v) //.
      iApply "Hinv". iIntros "_". iAlways. by iFrame "Hv".
    - rewrite big_sepM_insert //. iFrame "Hinv". iAlways. by iFrame "Hv".
  Qed.

  (** Properties of sealing *)

  Lemma sealed_agree γ v1 v2 v' φ :
    is_sealed γ v1 v' φ -∗ is_sealed γ v2 v' φ -∗ ⌜v1 = v2⌝.
  Proof. iIntros "(_&_&%) (_&_&%)". by naive_solver. Qed.

  Lemma sealed_high p γ v v' k φ :
    {{{ is_sealed γ v v' φ ∗ k ↦ () ∗ fresh k }}} v' k @ p; ⊤
    {{{ RET (); is_witness (ghost γ) k v }}}.
  Proof.
    iIntros (Φ) "((#[Hh Hsync] & Hv & %) & Hk & Hf) HΦ". subst. wp_lam.
    wp_typecast Hloc; last by exfalso; apply Hloc; exists k.
      wp_match. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & Hm & Hw & #Hinv)". wp_load.
    wp_apply (map_insert_spec _ _ _ m with "Hm").
      iIntros (map') "Hm'". rewrite -wp_fupd. wp_store.
    iMod (witness_high _ _ k v with "Hh Hw Hk Hf") as "[Hw Hkv]".
    iApply ("HΨ" with "[Hv Hl Hm' Hw]"); last by iApply ("HΦ" with "Hkv").
    iExists map', (<[k:=v]> m). iFrame "Hl Hm' Hw".
    by iApply (tbl_inv_insert with "Hinv Hv").
  Qed.

  Lemma sealed_inv γ v v' φ : is_sealed γ v v' φ -∗ φ v.
  Proof. iIntros "(_ &#Hv&_)". by iFrame "Hv". Qed.

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
    - rewrite (low_val k). by iApply (witness_low with "Hw Hk").
    - by iApply (tbl_inv_insert with "Hinv [Hv]").
  Qed.

  Lemma seal_low γ s φ : is_seal γ s φ -∗ □ (∀ v, low v -∗ φ v) -∗ low s.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v Φ) "#Hv HΦ". simpl_subst. wp_value.
    iApply "HΦ".
    iApply (sealed_low γ v with "[]"). iFrame "Hctx".
    iSplitL; last done. iAlways. by iApply ("Hφ" with "Hv").
  Qed.

  (** Properties of unsealing. *)

  Lemma unseal_body_low γ v' φ :
    {{{ ctx γ φ ∗ low v' }}}
      let: "k" := ref () in
      v' "k" ;;
      (sync γ) (λ: <>, (map_lookup_partial ! (tbl γ)) "k")
    ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "(#[Hh Hsync] & #Hv') HΦ".
    wp_apply (wp_alloc_low with "[$Hh]"); auto; first by simpl_low.
      iIntros (k) "Hk". wp_let.
    (* PDS: Hack. *)
    (*
     * [wp_on_val_app] should be a Texan triple and there's no call to
     * state those lemmas in terms of expressions.
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

  Lemma unseal_low γ u φ :
    is_unseal γ u φ -∗ □ (∀ v, φ v -∗ low v) -∗ low u.
  Proof.
    iIntros "[#Hctx %] #Hφ". subst. rewrite low_rec.
      iAlways. iNext. iIntros (v' Φ) "#Hv' HΦ". simpl_subst.
    wp_apply (unseal_body_low with "[$Hctx $Hv']"). iIntros (v) "Hv".
    iApply "HΦ". by iApply ("Hφ" with "Hv").
  Qed.

  (** Operations *)

  Lemma make_seal_spec N p φ :
    heapN ⊥ N →
    {{{ heap_ctx }}} code.make_seal () @ p; ⊤
    {{{ v1 v2 γ, RET (v1, v2); is_seal γ v1 φ ∗ is_unseal γ v2 φ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc l as "Hl". wp_let.
      rewrite -wp_fupd. set h := to_heap ∅.
    iMod (own_alloc (Auth (Excl' h) h)) as (γh) "Hγh"; first done.
      rewrite (auth_both_op h). iDestruct "Hγh" as "[Hγh _]".
    iAssert (witness γh ∅) with "[Hγh]" as "Hw".
    { iExists ∅. iFrame "Hγh".
      rewrite dom_empty_L big_sepS_empty big_sepM_empty. by auto. }
    wp_apply (make_sync_spec L _ N (tbl_res l γh φ) with "[$Hh Hl Hw]");
      first done.
    { iExists map_empty, ∅. iFrame "Hl Hw". rewrite big_sepM_empty. by auto. }
    iIntros (sync) "#Hsync". iCombine "Hh" "Hsync" as "Hctx".
      set γ := {| sync := sync; tbl := l; ghost := γh |}. do 3!wp_let.
    iApply ("HΦ" $! _ _ γ). iFrame "Hctx Hctx". by auto.
  Qed.

  Lemma seal_spec p γ s v φ `{!PersistentP (φ v)} :
    {{{ is_seal γ s φ ∗ φ v }}} s v @ p; ⊤
    {{{ v', RET v'; is_sealed γ v v' φ }}}.
  Proof.
    iIntros (Φ) "[[#Hctx %] #Hv] HΦ". subst. wp_lam.
    iApply "HΦ". iFrame "Hctx". iSplitL. by iAlways. done.
  Qed.

  Lemma unseal_spec p γ u v v' φ :
    {{{ is_unseal γ u φ ∗ is_sealed γ v v' φ }}} u v' @ p; ⊤ {{{ RET v; φ v }}}.
  Proof.
    iIntros (Φ) "[[#[Hh Hsync] %] Hv'] HΦ". subst. wp_lam.
    wp_apply (wp_alloc_fresh with "Hh"); auto.
      iIntros (k) "[Hk Hf]". wp_let.
    wp_apply (sealed_high with "[$Hv' $Hk $Hf]"). iIntros "Hwk". wp_seq.
      rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (map m) "(Hl & #Hm & Hw & #Hinv)". wp_load.
      iDestruct (witness_elim with "Hw Hwk") as "%".
    wp_apply (map_lookup_partial_Some_spec _ _ _ _ k with "Hm");
      first done. iIntros "_".
    iApply ("HΨ" with "[Hl Hw]").
    - iExists map, m. by iFrame "Hl Hm Hw Hinv".
    - iApply "HΦ". setoid_rewrite always_elim.
      by iApply (big_sepM_lookup (λ _, φ) m k v with "Hinv").
  Qed.

  Lemma unseal_low_spec γ u v' φ :
    {{{ is_unseal γ u φ ∗ low v' }}} u v' ?{{{ v, RET v; φ v }}}.
  Proof.
    iIntros (Φ) "[[Hctx %] Hv'] HΦ". subst. wp_lam.
    by wp_apply (unseal_body_low with "[$Hctx $Hv'] [$HΦ]").
  Qed.

  Definition sealing : sealing Σ := {|
    intf.seal_low := seal_low;
    intf.unseal_low := unseal_low;
    intf.sealed_low := sealed_low;
    intf.sealed_inv := sealed_inv;
    intf.make_seal_spec := make_seal_spec;
    intf.seal_spec := seal_spec;
    intf.unseal_spec := unseal_spec;
    intf.unseal_low_spec := unseal_low_spec
  |}.
End proof.
End proof.
