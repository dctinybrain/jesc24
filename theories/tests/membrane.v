From iris.algebra Require Import auth gmap coPset.
From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import membrane abort lock.
From iris.tests Require Import maps.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

(* PDS: Neither LockImpl nor CaretakerImpl should be type classes. *)
(* PDS: Heap should actually define [lowval]. *)
(*
	PDS: The language should define [CoInductive loc := Loc of
	positive] so that we can write [gsetUR loc] rather than the
	inscrutible [coPsetUR].
*)

(* PDS: Addenda. *)
Section coPset.	(* addendum, someone forgot to note persistence *)
  From iris.algebra Require Import coPset auth.
  Implicit Types X : coPset.

  Global Instance coPset_persistent X : Persistent X.
  Proof. by apply persistent_total. Qed.
End coPset.

Section auth.
Context {A : ucmraT}.
Implicit Types a b : A.
Implicit Types x y : auth A.

Lemma auth_frag_alloc a b `{!CMRADiscrete A, !CMRATotal A}
    (HA : ∀ x : A, Persistent x) :
  b ≼ a → ● a ~~> ● a ⋅ ◯ b.
Proof.
  move=>[a' ->]. apply auth_update_alloc.
  rewrite -{3}(persistent_core b) -(right_id _ _ (core b)).
  rewrite -{2}(cmra_core_l b) -assoc.
  apply op_local_update_discrete.
  by rewrite assoc cmra_core_l.
Qed.
End auth.

(** * Public membrane interface *)
(**
	As a matter of policy, we use [pub_ref] to "declare" _public
	locations_. Public locations work like high-integrity
	locations with two exceptions. Ownership of public locations
	is exclusive rather than fractional as that suffices for our
	toy client. (The richer interface is sound, of course, but
	fractional permissions would go unused.) More important, each
	public location has a unique, low-integrity _shadow location_
	serving as its proxy for use in adversarial code.

	Public locations lift as _public values_. The total function
	[pub_wrap] convert a public value to its low-integrity
	counterpart by replacing public locations with their shadows.
	Its partial inverse is [pub_unwrap].

	The functions [shadow_read] and [shadow_write] read from and
	write to a public location's shadow. These functions handle
	wrapping and unwrapping; for example, the value returned by
	[shadow_read] is a public value.
*)

Module Import public_membrane.
  (** ** Operations *)
  Record PubImpl : Set := pub_impl {
    make_pub : val;
    pub_ref : val;
    pub_wrap : val;
    pub_unwrap : val;
    shadow_read : val;
    shadow_write : val
  }.

  Section spec.
    Context `{heapG Σ} {PI : PubImpl}.
    Notation lowval := (low : val → iProp Σ).

    Structure pub := Pub {
      (** Predicates *)
      (** Name ties [is_pub] and [own_pub] to [is_membrane]. *)
      name : Type;
      is_membrane (N : namespace) (γ : name) (m : val) : iProp Σ;
      is_pub (γ : name) (l : loc) : iProp Σ;
      own_pub (γ : name) (l : loc) (v : val) : iProp Σ;
      (** Structure *)
      is_membrane_persistent N γ m : PersistentP (is_membrane N γ m);
      is_pub_timeless γ l : TimelessP (is_pub γ l);
      is_pub_persistent γ l : PersistentP (is_pub γ l);
      own_pub_timeless γ l v : TimelessP (own_pub γ l v);
      (** Public ownership *)
      own_pub_pub γ l v : own_pub γ l v ⊢ is_pub γ l;
      own_pub_exclusive γ l v1 v2 : own_pub γ l v1 ∗ own_pub γ l v2 ⊢ False;
      open_pub γ l v : own_pub γ l v ⊢ l ↦ v ∗ (∀ w, l ↦ w -∗ own_pub γ l w);
      (** Operations *)
      make_pub_spec N :
        heapN ⊥ N →
        {{{ heap_ctx }}} make_pub PI () {{{ m γ, RET m; is_membrane N γ m }}};
      pub_alloc_spec N γ m (v : val) :
        {{{ is_membrane N γ m ∗ on_val (is_pub γ) v }}} pub_ref PI m v
        {{{ l, RET LocV l; own_pub γ l v }}};
      pub_wrap_spec N γ m v1 :
        {{{ is_membrane N γ m ∗ on_val (is_pub γ) v1 }}} pub_wrap PI m v1
        {{{ v2, RET v2; low v2 }}};
      pub_unwrap_spec N γ m v2 :
        {{{ is_membrane N γ m ∗ lowval v2 }}} pub_unwrap PI m v2
        ?{{{ v1, RET v1; on_val (is_pub γ) v1 }}};
      shadow_read_spec N γ m l :
        {{{ is_membrane N γ m ∗ is_pub γ l }}} shadow_read PI m l
        {{{ v, RET v; on_val (is_pub γ) v }}};
      shadow_write_spec N γ m l v :
        {{{ is_membrane N γ m ∗ is_pub γ l ∗ on_val (is_pub γ) v }}}
          shadow_write PI m l v
        {{{ RET (); True }}}
    }.
  End spec.
  Arguments pub _ {_ _}.
  Existing Instances is_membrane_persistent is_pub_timeless
    is_pub_persistent own_pub_timeless.
End public_membrane.

(** * Code *)
Section pub_code.
  Context {LI : LockImpl}.

  Definition make_pub : val := λ: "locin",
    let: "tbl" := ref bij_empty in
    let: "sync" := make_sync LI () in
    ("sync", "tbl").
  Definition locout : val := λ: "m" "l1",
    let: "sync" := Fst "m" in let: "tbl" := Snd "m" in
    "sync" (λ: <>, bij_lookup_partial (! "tbl") "l1").
  Definition locin : val := λ: "m" "l2",
    let: "sync" := Fst "m" in let: "tbl" := Snd "m" in
    "sync" (λ: <>, bij_lookup_partial (bij_invert (! "tbl")) "l2").
  Definition pub_wrap : val := λ: "m", membrane (locout "m") (locin "m").
  Definition pub_unwrap : val := λ: "m", membrane (locin "m") (locout "m").
  Definition pub_ref : val := λ: "m" "x1",
    let: "x2" := pub_wrap "m" "x1" in
    let: "sync" := Fst "m" in let: "tbl" := Snd "m" in
    "sync" (λ: <>,
      let: "r1" := ref "x1" in
      let: "r2" := ref "x2" in
      "tbl" <- bij_insert_new (! "tbl") "r1" "r2";;
      "r1"
    ).
  Definition shadow_read : val := λ: "m" "l",
    pub_unwrap "m" (! locout "m" "l").
  Definition shadow_write : val := λ: "m" "l" "x",
    locout "m" "l" <- pub_wrap "m" "x".
End pub_code.

(** The CMRA we need. *)
(**
	We use tokens during allocation, where we have to show that a
	freshly allocated location isn't in the membrane's table.
 *)
Local Notation locset := coPsetUR.
Local Notation tokmap := (gmapUR loc (exclR unitC)).
Class pubG Σ := PubG {
  pub_locsG :> inG Σ (authR locset);
  pub_toksG :> inG Σ (authR tokmap)
}.
Definition pubΣ : gFunctors := #[
  GFunctor (constRF (authR locset));
  GFunctor (constRF (authR tokmap))
].

Instance subG_pubΣ {Σ} : subG pubΣ Σ → pubG Σ.
Proof. intros [??]%subG_inv; constructor; apply _. Qed.

Section pub_proof.
  Context `{heapG Σ, pubG Σ, LI : LockImpl} (L : lock Σ).
  Context (N : namespace).

  (** Definitions *)

  Definition name : Type := gname * gname.

  Definition is_pub (γ : name) (l : loc) : iProp Σ := own (γ.1) (◯ ({[ l ]})).

  Definition own_tok (γ : name) (l : loc) : iProp Σ :=
    own (γ.2) (◯ ({[ l := Excl () ]})).

  Definition own_pub (γ : name) (l : loc) (v : val) : iProp Σ :=
    (is_pub γ l ∗ l ↦ v ∗ own_tok γ l)%I.

  Definition to_tok : gmap loc val → tokmap := fmap (λ v, Excl ()).

  Definition pubhigh (γ : name) (m1 : gmap loc val) : iProp Σ :=
    (own (γ.1) (● (dom _ m1)) ∗ own (γ.2) (● to_tok m1))%I.

  Definition publow (m2 : gmap loc val) : iProp Σ :=
    ([∗ map] l2↦_ ∈ m2, low l2)%I.

  Definition tbl_res (t : loc) (γ : name) : iProp Σ := (
    ∃ bij m1 m2, t ↦ bij ∗ ⌜is_bij bij m1 m2⌝ ∗
    pubhigh γ m1 ∗ publow m2
  )%I.

  Definition is_membrane (γ : name) (m : val) : iProp Σ := (
    ∃ (t : loc) sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜m = (sync, t)%V⌝ ∗
    is_sync sync (tbl_res t γ)
  )%I.

  (** Structure and logical moves *)

  Global Instance is_membrane_persistent γ m :
    PersistentP (is_membrane γ m).
  Proof. apply _. Qed.
  Global Instance is_pub_timeless γ l : TimelessP (is_pub γ l).
  Proof. apply _. Qed.
  Global Instance is_pub_persistent γ l : PersistentP (is_pub γ l).
  Proof. apply _. Qed.
  Global Instance own_pub_timeless γ l v : TimelessP (own_pub γ l v).
  Proof. apply _. Qed.

  Lemma pubhigh_obs γ m1 l1 :
    is_Some (m1 !! l1) →
    pubhigh γ m1 ==∗ pubhigh γ m1 ∗ is_pub γ l1.
  Proof.
    iIntros (?) "(Hpub & Htok)". rewrite/pubhigh /is_pub. iFrame "Htok".
    rewrite -own_op. iApply (own_update with "Hpub").
    apply auth_frag_alloc; try apply _.
    by apply coPset_included, elem_of_subseteq_singleton, elem_of_dom.
  Qed.

  Lemma own_pub_pub γ l v : own_pub γ l v ⊢ is_pub γ l.
  Proof. rewrite/own_pub. by iIntros "(?&_&_)". Qed.

  Lemma own_pub_exclusive γ l v1 v2 :
    own_pub γ l v1 ∗ own_pub γ l v2 ⊢ False.
  Proof.
    rewrite/own_pub. iIntros "((_ &Hl1&_) & (_&Hl2&_))".
    iDestruct (mapsto_valid_2 with "[$Hl1 $Hl2]") as "Hv".
    iDestruct "Hv" as %Hv. by case: Hv.
  Qed.

  Lemma open_pub γ l v :
    own_pub γ l v ⊢ l ↦ v ∗ (∀ w, l ↦ w -∗ own_pub γ l w).
  Proof.
    rewrite/own_pub. iIntros "(Hp&Hl&Htok)". iFrame "Hl Htok".
    iIntros (w) "Hl". by iFrame "Hp Hl".
  Qed.

  (** Operations *)

  Lemma make_pub_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_pub () {{{ m γ, RET m; is_membrane γ m }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc t as "Ht". wp_let.
      rewrite -wp_fupd. set T := to_tok ∅.
    iMod (own_alloc (Auth (Excl' ∅) (∅ : locset))) as (γ1) "Hγ1"; first done.
    iMod (own_alloc (Auth (Excl' T) T)) as (γ2) "Hγ2"; first done.
      rewrite (auth_both_op T _). iDestruct "Hγ2" as "[Hγ2 _]".
    wp_apply (make_sync_spec L _ _ (tbl_res t (γ1, γ2)) with "[$Hh Ht Hγ1 Hγ2]").
    - solve_ndisj.
    - iExists bij_empty, ∅, ∅.
      rewrite /pubhigh dom_empty /publow big_sepM_empty.
      iFrame "Ht Hγ1 Hγ2". iPureIntro. exact: bij_empty_spec.
    iIntros (sync) "#Hsync". wp_let. iModIntro.
    iApply ("HΦ" $! _ (γ1, γ2)). iExists t, sync. by iFrame "% Hh Hsync".
  Qed.

  Lemma locout_spec p E γ m :
    {{{ is_membrane γ m }}} locout m @ p; E
    {{{ v, RET v; is_monPV progress v (is_pub γ) low }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (l1) "!#". iIntros (Φ) "Hl1 HΦ".
      wp_lam.
    iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & [Hlocs Htoks] & #Hlo)".
      wp_load.
    iDestruct (own_valid_2 with "Hlocs Hl1") as %
      [(v1&?)%coPset_included%elem_of_subseteq_singleton
       %elem_of_dom ?]%auth_valid_discrete_2.
    wp_apply (bij_lookup_partial_Some_spec _ _ _ _ _ l1 with "Hbij")=>//.
      iIntros (l2) "[%%]". subst.
      iDestruct (big_sepM_lookup _ _ l2 with "Hlo") as "Hl2"=>//.
    iApply ("HΨ" with "[Ht Hlocs Htoks]").
    - iExists bij, m1, m2. by iFrame "Ht Hbij Hlocs Htoks Hlo".
    by iApply ("HΦ" with "Hl2").
  Qed.

  Lemma locout_mon γ m :
    is_membrane γ m -∗ is_monP progress (locout m) (is_pub γ) low.
  Proof.
    iIntros "#Hm". rewrite monP_triple. iAlways. iIntros (p0 E0 Φ) "HΦ".
    wp_apply (locout_spec with "Hm"). iIntros (vout) "Hout".
    by iApply ("HΦ" with "Hout").
  Qed.

  Lemma locin_spec p E γ m :
    {{{ is_membrane γ m }}} locin m @ p; E
    {{{ v, RET v; is_monPV noprogress v low (is_pub γ) }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (l2) "!#". iIntros (Φ) "Hl2 HΦ".
      wp_lam.
    iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & Hhi & #Hlo)". wp_load.
    wp_apply (bij_invert_spec _ _ _ m1 m2 with "Hbij").
      iIntros (bij') "#Hbij'". rewrite -wp_fupd.
    wp_apply (bij_lookup_partial_spec _ _ m2 m1 with "Hbij'").
      iIntros (l1) "[%%]".
    iMod (pubhigh_obs _ _ l1 with "Hhi") as "[Hhi Hl1]"; first by exists l2.
    iApply ("HΨ" with "[Ht Hhi]").
    - iExists bij, m1, m2. by iFrame "Ht Hbij Hhi Hlo".
    by iApply ("HΦ" with "Hl1").
  Qed.

  Lemma locin_mon γ m :
    is_membrane γ m -∗ is_monP noprogress (locin m) low (is_pub γ).
  Proof.
    iIntros "#Hm". rewrite monP_triple. iAlways. iIntros (p0 E0 Φ) "HΦ".
    wp_apply (locin_spec with "Hm"). iExact "HΦ".
  Qed.

  Lemma pub_wrap_spec γ m v1 :
    {{{ is_membrane γ m ∗ on_val (is_pub γ) v1 }}} pub_wrap m v1
    {{{ v2, RET v2; low v2 }}}.
  Proof.
    iIntros (Φ) "(#Hm & Hv1) HΦ". wp_lam.
    wp_apply (membrane_spec _ _ progress _ (is_pub γ) low with "[]").
    - by iApply (locout_mon with "Hm").
    iIntros (w) "Hw".
    wp_apply ("Hw" $! _ _ noprogress with "* []").
    - by iApply (locin_mon with "Hm").
    iIntros (wrap) "Hwrap". rewrite monPV_triple.
    wp_apply ("Hwrap" with "* Hv1"). iExact "HΦ".
  Qed.

  Lemma pub_unwrap_spec γ m (v2 : val) :
    {{{ is_membrane γ m ∗ low v2 }}} pub_unwrap m v2
    ?{{{ v1, RET v1; on_val (is_pub γ) v1 }}}.
  Proof.
    iIntros (Φ) "(#Hm & Hv2) HΦ". wp_lam.
    wp_apply (membrane_spec _ _ noprogress _ low (is_pub γ) with "[]").
    - by iApply (locin_mon with "Hm").
    iIntros (u) "Hu".
    wp_apply ("Hu" $! _ _ progress with "* []").
    - by iApply (locout_mon with "Hm").
    iIntros (unwrap) "Hunwrap". rewrite monPV_triple.
    wp_apply ("Hunwrap" with "* Hv2"). iExact "HΦ".
  Qed.

  Lemma pub_alloc_spec γ m (v : val) :
    {{{ is_membrane γ m ∗ on_val (is_pub γ) v }}} pub_ref m v
    {{{ l, RET LocV l; own_pub γ l v }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hv) HΦ". wp_lam. wp_lam.
    wp_apply (pub_wrap_spec with "[$Hm $Hv]"). iIntros (v2) "Hv2".
      wp_let.
    iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & Hhi & #Hlo)".
    wp_alloc l1 as "Hl1". wp_let.
    wp_apply (wp_alloc_low with "[$Hh $Hv2]"); auto.
      iIntros (l2) "Hl2". wp_let. wp_load.
(*
	As l2 initially high, we can easily show l2 ∉ dom m2 = rng m1.
	Proving l1 ∉ dom m1 is another matter.

	For this proof to go through, I think we need to extend the
	heap interface to speak of locations that exist in the state:

		[is_alloced l](h, g) ≈ l ∈ dom h

	l ↦ v ⊢ is_alloced l
	low l ⊢ is_alloced l
	{ [∗ set] l ∈ X, is_alloced l } ref v {l, RET l; l ↦ v ∗ l ∉ X}

	(Retain the simpler high allocation triple for use with wp_alloc.)

	Tokens were a mistake. We can then extend tbl_res with
	knowledge that every location in m1 has been allocated:

		[∗ set] l ∈ dom m1, is_alloced l

	On allocating l1, we learn l1 ∉ dom m1.
*)
​"Hhi" : own (γ.1) (● dom locset m1) ∗ own (γ.2) (● to_tok m1)
​"Hl1" : l1 ↦ v
​"Hl2" : low l2
—
⌜m1 !! l1 = None⌝ ∗ ⌜m2 !! l2 = None⌝

​"Hhi" : pubhigh γ m1
—
pubhigh γ (<[l1 := l2]> m1)



    wp_apply (bij_insert_new_spec _ _ _ l1 l2 with "* [$Hbij]").

    - iIntros (bij') "Hbij'". wp_store.
      iApply ("HΨ" with "[Ht Hbij' Hhi]"). iExists _, _, _. iFrame "Ht Hbij'".

      wp_proj. wp_let. wp_proj. wp_let.
    rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
    iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & Hhi & Hlo)".
      wp_alloc l as "Hl". wp_let.	(* PDS: Need wrap sec. *)

  shadow_read_spec N γ m l :
    {{{ is_membrane N γ m ∗ publoc γ l }}} shadow_read PI m l
    {{{ v, RET v; on_val (publoc γ) v }}};
  shadow_write_spec N γ m l v :
    {{{ is_membrane N γ m ∗ publoc γ l ∗ on_val (publoc γ) v }}}
      shadow_write PI m l v
    {{{ RET (); True }}};
  (* PDS: This operation should not get stuck. *)
  pub_wrap_spec N γ m v1 :
    {{{ is_membrane N γ m ∗ on_val (publoc γ) v1 }}} pub_wrap PI m v1
    ?{{{ v2, RET v2; low v2 }}};
  pub_unwrap_spec N γ m v2 :
    {{{ is_membrane N γ m ∗ lowval v2 }}} pub_unwrap PI m v2
    ?{{{ v1, RET v1; on_val (publoc γ) v1 }}}.

  (* PDS: Consider making [is_locout] a predicate on expressions. *)
  Lemma locout_spec l :
    {{{ proxy_res l }}} locout l {{{ v, RET v; is_locout v Ψ }}}.
  Admitted.

  (* PDS: is_unwrap, is_wrap should put Ψ after v. *)

  Definition is_get (g : val) : iProp Σ :=
    (∀ l1, {{{ Ψ l1 }}} g l1 {{{ v1, RET v1; on_val Ψ v1 }}})%I.

  Lemma get_spec l w u :
    {{{ proxy_res l ∗ is_wrap Ψ w ∗ is_unwrap Ψ u }}}
      get_unsafe l w u
    {{{ g, RET g; is_unsafe_get g }}}.
  Admitted.

  Definition is_unsafe_put (p : val) : iProp Σ :=
    (∀ l1 v1, {{{ Ψ l1 ∗ on_val Ψ v1 }}} p l1 v1 {{{ RET (); True }}})%I.

  Lemma put_unsafe_spec l w :
    {{{ proxy_res l ∗ is_wrap Ψ w }}} put_unsafe l w
    {{{ p, RET p; is_unsafe_put p }}}.
  Admitted.

  Definition is_proxy_locin (vin : val) : iProp Σ :=
    (∀ l, {{{ proxy_res l }}} vin l {{{ v, RET v; is_locin v Ψ }}})%I.

  Lemma locin_fail_spec : is_proxy_locin locin_fail.
  Admitted.

  Lemma locin_alloc_spec : is_proxy_locin locin_alloc.
  Admitted.

  Lemma make_proxy_spec (vin : val) :
    {{{ is_proxy_locin vin }}} make_proxy vin
    {{{ w g p, RET (w, g, p);
      is_wrap Ψ w ∗ is_unsafe_get g ∗ is_unsafe_put p }}}.
  Admitted.
End proxy_proof.


(*
OK: Do something with it!

	• pblic locations are is_pub
	• ow, they are ghosts backed by a real location (in an invariant)
	and can be used to modify the heap
	• on wrapping, a public location's contents are also
	wrapped and overwrite the shadow

	Buffer gap (offsets only) with private state but with a public
	limit on length that can grow but not shrink:

		let limit = pubref 50 in
		(* Invariant: 0 ≤ gapbeg ≤ gapend ≤ size *)
		(* Invariant: logical length ≤ get_limit() *)
		let gapbeg = ref 0
		let gapend = ref 1
		let size = ref 1
		let sync = make_sycn()
			(* protecting limit, gapbeg, gapend, size *)
		let _get_limit = λ (),
			let prev = ! limit in
			let next =
				if isint: (shadow_read limit) as n =>
					if n < prev then prev else n
				else prev
			in
			assert (prev <= next);
			limit <- next;
			shadow_write limit next;	(* inform our clients *)
			next
		in
		let _length () =
			let n = ! size - (! gapend - ! gapbeg) in
			assert 0 ≤ n ≤ get_limit(); n
		in
		let _move i =
			assert 0 ≤ i ≤ _length();
			let b = !gapbeg in
			if i = b then ()
			else if i < b then
				let n = b - i in
				let e = !gapend - n in
				(* blit *)
				gapbeg <- i;
				gapend <- e
			else
				let n = i - b in
				(* blit *)
				gapbeg <- i;
				gapend <- !gapend + n
		let _grow () =
			assume _length() < _get_limit();
			let gapsz = !gapend - !gapbeg in
			if gapsz ≥ 1 then () else
			let n = !size in
			let bufsz = n + n in
			size <- bufsz;
			gapend <- gapbeg + 1
		in
		let _insert i = move i; grow (); gapbeg <- i+1 in
		let _delete i = move (i + 1); gapbeg <- i in
		let _pubinsert i = assume 0 ≤ i <= length(); insert i in
		let _pubdelete i = assume 0 ≤ i < length(); delete i in
		let priv = (sync nsert, sync delete) in
		let pub = (limit, sync _pubinsert, sync _pubdelete) in
		(priv, pub_wrap pub)
*)










(*


(** * Proxy *)
(**
	A membrane that memoizes wrapping decisions and offers
	[unsafe_get] and [unsafe_put] for interfering with adversarial
	locations.
*)

Definition locout : val := λ: "r" "wrap" "l1",
  let: "f" := ! "r" in
  match: bij_lookup "f" "l1" with
    SOME "l2" => "l2"
  | NONE =>
    let: "l2" := ref () in
    let: "f" := bij_insert_new "f" "l1" "l2" in
    "r" <- "f" ;;
    "l2" <- "wrap" (! "l1") ;;
    "l2"
  end.

Definition get_unsafe : val := λ: "r" "wrap" "unwrap" "l1",
  let: "l2" := locout "r" "wrap" "l1" in
  "unwrap" (! "l2").

Definition put_unsafe : val := λ: "r" "wrap" "l1" "v1",
  let: "l2" := locout "r" "wrap" "l1" in
  "l2" <- "wrap" "v1".

Definition locin_fail : val := λ: "r" <> "l2",
  match: bij_lookup (bij_invert (! "r")) "l2" with
    SOME "l1" => "l1"
  | NONE => abort	(* we could allocate. *)
  end.

Definition locin_alloc : val := λ: "r" "unwrap" "l2",
  let: "f" := bij_invert (! "r") in
  match: bij_lookup "f" "l2" with
    SOME "l1" => "l1"
  | NONE =>
    let: "l1" := ref () in
    let: "f" := bij_insert_new "f" "l2" "l1" in
    "r" <- bij_invert "f" ;;
    (* Unwrap after recording [l1 ↔ l2]. *)
    "l1" <- "unwrap" (! "l2") ;;
    "l1"
  end.

Section proxy_code.
  Context {LI : LockImpl}.

  Definition make_proxy : val := λ: "locin",
    let: "r" := ref bij_empty in
    let: "sync" := make_sync LI () in
    let: "wrap" := membrane (locout "r") ("locin" "r") in
    let: "unwrap" := membrane ("locin" "r") (locout "r") in
    let: "get" := λ: "l1", "sync" (λ: <>, get_unsafe "r" "wrap" "unwrap" "l1") in
    let: "put" := λ: "l1" "v1", "sync" (λ: <>, put_unsafe "r" "wrap" "l1" "v1") in
    let: "wrap" := λ: "v1", "sync" (λ: <>, "wrap" "v1") in
    ("wrap", "get", "put").

  Definition proxy_fail : expr := make_proxy locin_fail.
  Definition proxy_alloc : expr := make_proxy locin_alloc.
End proxy_code.

Section proxy_proof.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ).
  Context (Ψ : loc → iProp Σ).
  Import membrane_spec.

  Instance LocV_inj : Inj (=) (=) LocV. Proof. by move=>??[]->. Qed.

  Definition proxy_res (l : loc) : iProp Σ := (
    ∃ bij m1 m2, l ↦ bij ∗ ⌜is_bij LocV bij m1 m2⌝ ∗
    ([∗ map] l1↦_ ∈ m1, Ψ l1) ∗ ([∗ map] l2↦_ ∈ m1, low l2)
  )%I.

  (* PDS: Consider making [is_locout] a predicate on expressions. *)
  Lemma locout_spec l :
    {{{ proxy_res l }}} locout l {{{ v, RET v; is_locout v Ψ }}}.
  Admitted.

  (* PDS: is_unwrap, is_wrap should put Ψ after v. *)

  Definition is_unsafe_get (g : val) : iProp Σ :=
    (∀ l1, {{{ Ψ l1 }}} g l1 {{{ v1, RET v1; on_val Ψ v1 }}})%I.

  Lemma get_unsafe_spec l w u :
    {{{ proxy_res l ∗ is_wrap Ψ w ∗ is_unwrap Ψ u }}}
      get_unsafe l w u
    {{{ g, RET g; is_unsafe_get g }}}.
  Admitted.

  Definition is_unsafe_put (p : val) : iProp Σ :=
    (∀ l1 v1, {{{ Ψ l1 ∗ on_val Ψ v1 }}} p l1 v1 {{{ RET (); True }}})%I.

  Lemma put_unsafe_spec l w :
    {{{ proxy_res l ∗ is_wrap Ψ w }}} put_unsafe l w
    {{{ p, RET p; is_unsafe_put p }}}.
  Admitted.

  Definition is_proxy_locin (vin : val) : iProp Σ :=
    (∀ l, {{{ proxy_res l }}} vin l {{{ v, RET v; is_locin v Ψ }}})%I.

  Lemma locin_fail_spec : is_proxy_locin locin_fail.
  Admitted.

  Lemma locin_alloc_spec : is_proxy_locin locin_alloc.
  Admitted.

  Lemma make_proxy_spec (vin : val) :
    {{{ is_proxy_locin vin }}} make_proxy vin
    {{{ w g p, RET (w, g, p);
      is_wrap Ψ w ∗ is_unsafe_get g ∗ is_unsafe_put p }}}.
  Admitted.
End proxy_proof.
*)
