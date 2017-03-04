From iris.algebra Require Import auth gmap coPset.
From iris.heap_lang Require addenda.
From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import membrane abort assume lock.
From iris.tests Require Import maps.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred addenda.algebra_auth.

(* PDS: We'll probably need PubImpl a Class when we link the client. *)
(* PDS: Heap should actually define [lowval]. *)

(** * Public membrane interface *)
(**
	As a matter of policy, we use [pub_ref] to "declare" _public
	locations_. Each public location has a unique, low-integrity
	_shadow location_ serving as its proxy for use in adversarial
	code.

	Public locations lift as _public values_. The total function
	[pub_wrap] convert a public value to its low-integrity
	counterpart by replacing public locations with their shadows.
	Its partial inverse is [pub_unwrap].

	The functions [shadow_read] and [shadow_write] read from and
	write to a public location's shadow. These functions handle
	wrapping and unwrapping; for example, the value returned by
	[shadow_read] is a public value.
*)

Module Import intf.
(** Operations *)
Record PubImpl : Set := {
  make_pub : val; pub_ref : val; pub_wrap : val; pub_unwrap : val;
  shadow_read : val; shadow_write : val
}.

Section spec.
  Context `{heapG Σ} {PI : PubImpl}.
  Notation lowval := (low : val → iProp Σ).
  Implicit Types v f : val.

  (** PDS: What we need from the heap interface. *)
  Structure heap_extension := HeapExtension {
    is_alloced (l : loc) : iProp Σ;
    is_alloced_timeless l : TimelessP (is_alloced l);
    is_alloced_persistent l : PersistentP (is_alloced l);
    high_alloced (l : loc) (q : Qp) (v : val) : l ↦{q} v ⊢ is_alloced l;
    low_alloced (l : loc) : low l ⊢ is_alloced l;
    wp_alloc_fresh (p : pbit) (E : coPset) (e : expr) (v : val) (X : gset loc) :
      to_val e = Some v → ↑heapN ⊆ E →
      {{{ heap_ctx ∗ [∗ set] l ∈ X, is_alloced l }}} Alloc e @ p; E
      {{{ l, RET LocV l; l ↦ v ∗ ⌜l ∉ X⌝ }}};
    wp_alloc_low_fresh (p : pbit) (E : coPset) (e : expr) (v : val) (X : gset loc) :
      to_val e = Some v → ↑heapN ⊆ E →
      {{{ heap_ctx ∗ ▷ low v ∗  [∗ set] l ∈ X, is_alloced l }}} Alloc e @ p; E
      {{{ l, RET LocV l; low l ∗ ⌜l ∉ X⌝ }}}
  }.

  Structure pub := Pub {
    (** Predicates. Name ties [is_pub]  to [is_membrane]. *)
    name : Type;
    is_membrane (N : namespace) (γ : name) (m : val) : iProp Σ;
    is_pub (γ : name) (l : loc) : iProp Σ;
    (** Structure *)
    is_membrane_persistent N γ m : PersistentP (is_membrane N γ m);
    is_pub_timeless γ l : TimelessP (is_pub γ l);
    is_pub_persistent γ l : PersistentP (is_pub γ l);
    (** Operations *)
    make_pub_spec N :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_pub PI () {{{ m γ, RET m; is_membrane N γ m }}};
    pub_alloc_spec N γ m (v : val) :
      {{{ is_membrane N γ m ∗ on_val (is_pub γ) v }}} pub_ref PI m v
      {{{ l, RET LocV l; is_pub γ l ∗ l ↦ v }}};
    pub_wrap_spec N γ m p E :
      {{{ is_membrane N γ m }}} pub_wrap PI m @ p; E {{{ f, RET f;
        is_monP progress f (on_val (is_pub γ)) (on_val low)
      }}};
    pub_unwrap_spec N γ m p E :
      {{{ is_membrane N γ m }}} pub_unwrap PI m @ p; E {{{ f, RET f;
        is_monP noprogress f (on_val low) (on_val (is_pub γ))
      }}};
    shadow_read_spec N γ m l :
      {{{ is_membrane N γ m ∗ is_pub γ l }}} shadow_read PI m l
      ?{{{ v, RET v; on_val (is_pub γ) v }}};
    shadow_write_spec N γ m l v :
      {{{ is_membrane N γ m ∗ is_pub γ l ∗ on_val (is_pub γ) v }}}
        shadow_write PI m l v
      {{{ RET (); True }}}
  }.
End spec.
Arguments heap_extension _ {_}.
Existing Instances is_alloced_timeless is_alloced_persistent.
Arguments pub _ {_ _}.
Existing Instances is_membrane_persistent is_pub_timeless
  is_pub_persistent.
End intf.

(*
(** * Public membrane client *)
(**
	A counter with increment and decrement operations and public
	low and high bounds on the counter's value.
*)
Module client.
Section client.
  Context (LI : LockImpl) (PI : PubImpl).

  Definition get_limit : val := λ: "m" "limit",
    let: "prev" := ! "limit" in       (* PDS: isint: *)
    let: "n" := shadow_read PI "m" "limit" in
    let: "next" := if: "n" < "prev" then "prev" else "n" in
    assert: "prev" ≤ "next" ;;
    "limit" <- "next";; shadow_write PI "m" "limit" "next";;
    "next".

  Definition make_counter : val := λ: "m",
    let: "count" := ref #0 in
    let: "limit" := pub_ref PI "m" #10 in
    let: "sync" := make_sync LI () in
    let: "get" := "sync" (λ: <>, ! "count") in
    let: "inc" := "sync" (λ: <>,
      let: "n" := (! "count") + #1 in
      assume: "n" ≤ get_limit "m" "limit";;
      "count" <- "n"
    )
    in ("get", "inc", "limit").

    let: "limits" := λ: <>,
      let: "a" := "get" "lo" in
      let: "b" := "get" "hi" in
      let: "p" := if: "a" < "b" then ("a", "b") else ("b", "a") in
      let: "a" := Fst "p" in let: "b" := Snd "p" in
      assert: "a" ≤ "b" ;;
      "lo" <- "a";; shadow_write PI "m" "lo" "a" ;;
      "hi" <- "b";; shadow_write PI "m" "hi" "a" ;;
      "p"
    in
    let: "inc" :=
      "sync" (λ: <>,
        let: "n" := (! "count") + #1 in
        assume: "n" ≤ Snd ("limits" ());;
        "count" <- "n"
      )
    in
    let: "dec" :=
      "sync" (λ: <>,
        let: "n" := (! "count") - #1 in
        assume: "n" ≥ Fst ("limits" ());;
        "count" <- "n"
      )
    in
    ("inc", "dec", "lo", "hi")
    in ().

    let: "bounds" := "sync" (λ: <>,
      let: "prev_lo" := ! "lo" in
      let: "next_lo" :=
        if isint: (shadow_read PI "m" "lo") as n =>
          if n < prev then prev
    )
    in ().


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

    let: inc := "sync" (λ: <>,

End client.
End client.
*)

(** * Public membrane implementation *)
(**
	We maintain a partial bijection between public locations and
	their shadows. The table grows during allocation and matters
	during wrapping and unwrapping.
*)
Module code.
Section code.
  Context (LI : LockImpl).

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
    pub_unwrap "m" (! (locout "m" "l")).
  Definition shadow_write : val := λ: "m" "l" "x",
    locout "m" "l" <- pub_wrap "m" "x".
End code.

Definition pub_membrane (LI : LockImpl) : PubImpl := {|
  intf.make_pub := make_pub LI;
  intf.pub_ref := pub_ref;
  intf.pub_wrap := pub_wrap;
  intf.pub_unwrap := pub_unwrap;
  intf.shadow_read := shadow_read;
  intf.shadow_write := shadow_write
|}.
End code.

Module proof.
(** The CMRA we need. *)
Local Notation locset := (gsetUR loc).
Class pubG Σ := PubG { pub_locsG :> inG Σ (authR locset) }.
Definition pubΣ : gFunctors := #[ GFunctor (constRF (authR locset)) ].

Instance subG_pubΣ {Σ} : subG pubΣ Σ → pubG Σ.
Proof. intros [??]%subG_inv; constructor; apply _. Qed.

Section proof.
  Context `{heapG Σ, pubG Σ, LI : LockImpl}
    (EXT : heap_extension Σ) (L : lock Σ) (N : namespace).
  Let PI : PubImpl := code.pub_membrane LI.
  Implicit Types v f : val.

  (** Definitions *)

  Definition is_pub (γ : gname) (l : loc) : iProp Σ :=
    own γ (◯ (to_gset {[ l ]})).

  Definition pubhigh (γ : gname) (m1 : gmap loc val) : iProp Σ :=
    (own γ (● (dom (gset loc) m1)) ∗ [∗ set] l ∈ dom _ m1, is_alloced EXT l)%I.

  Definition publow (m2 : gmap loc val) : iProp Σ :=
    ([∗ set] l2 ∈ dom (gset loc) m2, low l2)%I.

  Definition tbl_res (t : loc) (γ : gname) : iProp Σ := (
    ∃ bij m1 m2, t ↦ bij ∗ ⌜is_bij bij m1 m2⌝ ∗ pubhigh γ m1 ∗ publow m2
  )%I.

  Definition is_membrane (γ : gname) (m : val) : iProp Σ := (
    ∃ (t : loc) sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜m = (sync, t)%V⌝ ∗
    is_sync sync (tbl_res t γ)
  )%I.

  (** Structure *)

  Global Instance is_membrane_persistent γ m :
    PersistentP (is_membrane γ m).
  Proof. apply _. Qed.
  Global Instance is_pub_timeless γ l : TimelessP (is_pub γ l).
  Proof. apply _. Qed.
  Global Instance is_pub_persistent γ l : PersistentP (is_pub γ l).
  Proof. apply _. Qed.

  (** Ghosts *)

  Lemma to_gset_included l (m : gmap loc val) :
    is_Some (m !! l) ↔ to_gset {[l]} ≼ dom (gset loc) m.
  Proof.
    split.
    - rewrite gset_included elem_of_subseteq=>??.
      rewrite elem_of_to_gset; last exact: singleton_finite.
      by rewrite elem_of_singleton elem_of_dom=>->.
    - rewrite gset_included=>/elem_of_subseteq/(_ l).
      rewrite elem_of_dom. apply. rewrite elem_of_to_gset.
      by rewrite elem_of_singleton. exact: singleton_finite.
  Qed.

  Lemma pubhigh_obs γ m1 l1 :
    is_Some (m1 !! l1) →
    pubhigh γ m1 ==∗ pubhigh γ m1 ∗ is_pub γ l1.
  Proof.
    iIntros (?) "(Hp & Ha)". rewrite/pubhigh/is_pub. iFrame "Ha".
    rewrite -own_op. iApply (own_update with "Hp").
    apply auth_frag_alloc; try apply _. by apply to_gset_included.
  Qed.

  Lemma pub_insert_dom {A} m (l : loc) (x : A) (Φ : loc → iProp Σ) :
    m !! l = None →
    ([∗ set] l ∈ dom (gset loc) m, Φ l) -∗ Φ l -∗
    [∗ set] l ∈ dom (gset loc) (<[l := x]> m), Φ l.
  Proof.
    iIntros (?) "Hm Hl". rewrite dom_insert_L big_sepS_union;
      last by rewrite disjoint_singleton_l not_elem_of_dom.
    rewrite big_sepS_singleton. by iFrame "Hm Hl".
  Qed.

  Lemma pubhigh_alloc γ m1 l1 l2 :
    m1 !! l1 = None →
    pubhigh γ m1 -∗ is_alloced EXT l1 ==∗ pubhigh γ (<[l1:=l2]> m1).
  Proof.
    iIntros (?) "(Hp&Ha) Ha1". rewrite/pubhigh.
    iSplitL "Hp"; last by iApply (pub_insert_dom with "Ha Ha1").
    rewrite -(own_mono _ _ (● dom (gset loc) (insert _ _ _)));
      last eapply cmra_included_l. iApply (own_update with "Hp").
    by eapply auth_update_alloc, gset_local_update,
      dom_insert_subseteq.
  Qed.

  Lemma publow_alloc m2 l1 l2 :
    m2 !! l2 = None →
    publow m2 -∗ low l2 -∗ publow (<[l2:=l1]> m2).
  Proof. exact: pub_insert_dom. Qed.

  (** Operations *)

  Lemma make_pub_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_pub PI () {{{ m γ, RET m; is_membrane γ m }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc t as "Ht". wp_let.
      rewrite -wp_fupd.
      iMod (own_alloc (Auth (Excl' ∅) ∅)) as (γ) "Hγ"; first done.
    wp_apply (make_sync_spec L _ _ (tbl_res t γ) with "[$Hh Ht Hγ]").
    - solve_ndisj.
    - iExists bij_empty, ∅, ∅.
      rewrite /pubhigh /publow dom_empty_L 2!big_sepS_empty.
      iFrame "Ht Hγ". iPureIntro. exact: bij_empty_spec.
    iIntros (sync) "#Hsync". wp_let. iModIntro.
    iApply ("HΦ" $! _ γ). iExists t, sync. by iFrame "% Hh Hsync".
  Qed.

  Lemma locout_spec p E γ m :
    {{{ is_membrane γ m }}} code.locout m @ p; E
    {{{ v, RET v; is_monP progress v (is_pub γ) low }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    iApply "HΦ". clear Φ p E. iIntros (l1) "!#". iIntros (Φ) "Hl1 HΦ". wp_lam.
      iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & [Hp Ha] & #Hlo)".
      wp_load.
      iDestruct (own_valid_2 with "Hp Hl1") as %
        [(v1&?)%to_gset_included ?]%auth_valid_discrete_2.
    wp_apply (bij_lookup_partial_Some_spec _ _ _ _ _ l1 with "Hbij")=>//.
      iIntros (l2) "[%%]". subst.
      iDestruct (big_sepS_elem_of _ _ l2 with "Hlo") as "Hl2";
        first by apply elem_of_dom; exists l1.
    iApply ("HΨ" with "[Ht Hp Ha]");
      first by iExists bij, m1, m2; iFrame "Ht Hbij Hp Ha Hlo".
    by iApply ("HΦ" with "Hl2").
  Qed.

  Lemma locin_spec p E γ m :
    {{{ is_membrane γ m }}} code.locin m @ p; E
    {{{ v, RET v; is_monP noprogress v low (is_pub γ) }}}.
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
    iApply ("HΨ" with "[Ht Hhi]");
      first by iExists bij, m1, m2; iFrame "Ht Hbij Hhi Hlo".
    by iApply ("HΦ" with "Hl1").
  Qed.

  Lemma pub_wrap_spec γ m p E :
    {{{ is_membrane γ m }}} pub_wrap PI m @ p; E {{{ f, RET f;
      is_monP progress f (on_val (is_pub γ)) (on_val low)
    }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    wp_apply (locout_spec with "Hm"). iIntros (locout) "Hlocout".
    wp_apply (membrane_spec with "Hlocout"). iIntros (w) "Hw".
    wp_apply (locin_spec with "Hm"). iIntros (locin) "Hlocin".
    wp_apply ("Hw" with "* Hlocin"). iExact "HΦ".
  Qed.

  Lemma pub_unwrap_spec γ m p E :
    {{{ is_membrane γ m }}} pub_unwrap PI m @ p; E {{{ f, RET f;
      is_monP noprogress f (on_val low) (on_val (is_pub γ))
    }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    wp_apply (locin_spec with "Hm"). iIntros (locin) "Hlocin".
    wp_apply (membrane_spec with "Hlocin"). iIntros (u) "Hu".
    wp_apply (locout_spec with "Hm"). iIntros (locout) "Hlocout".
    wp_apply ("Hu" with "* Hlocout"). iExact "HΦ".
  Qed.

  Lemma pub_alloc_spec γ m (v : val) :
    {{{ is_membrane γ m ∗ on_val (is_pub γ) v }}} pub_ref PI m v
    {{{ l, RET LocV l; is_pub γ l ∗ l ↦ v }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hv) HΦ". wp_lam. wp_lam.
    wp_apply (pub_wrap_spec with "Hm"). iIntros (wrap) "Hwrap".
      rewrite monP_triple.
    wp_apply ("Hwrap" $! v with "Hv"). iIntros (v2) "Hv2". wp_let.
      iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & (Hp & #Ha) & #Hlo)".
    wp_apply (wp_alloc_fresh with "[$Hh $Ha]"); auto.
      iIntros (l1) "(Hl1&Hm1)". iDestruct "Hm1" as %Hm1.
      wp_let.
    wp_apply (wp_alloc_low_fresh EXT _ _ _ _ (dom (gset loc) m2)
      with "[$Hh Hlo $Hv2]"); auto;
      first by iApply (big_sepS_mono' _ _ _ (low_alloced EXT) with "Hlo").
      iIntros (l2) "(#Hl2&Hm2)". iDestruct "Hm2" as %Hm2.
      wp_let. wp_load. rewrite -> not_elem_of_dom in Hm1, Hm2.
    wp_apply (bij_insert_new_spec _ _ _ l1 l2 with "* [$Hbij]"); auto.
      iIntros (bij') "{Hbij} #Hbij". rewrite -wp_fupd. wp_store.
      iDestruct (high_alloced EXT with "Hl1") as "#Ha1".
      iMod (pubhigh_alloc _ _ _ l2 with "[$Hp $Ha] Ha1") as "Hhi"=>//.
      iMod (pubhigh_obs with "Hhi") as "(Hhi & Hpub)";
        first by rewrite lookup_insert; exists l2. iModIntro.
      iDestruct (publow_alloc _ l1 with "Hlo Hl2") as "Hlo2"=>//.
    iApply ("HΨ" with "[Ht Hhi Hlo2]");
      first by iExists _, _, _; iFrame "Ht Hbij Hhi Hlo2".
    by iApply ("HΦ" with "[$Hpub $Hl1]").
  Qed.

  Lemma shadow_write_spec γ m l v :
    {{{ is_membrane γ m ∗ is_pub γ l ∗ on_val (is_pub γ) v }}}
      shadow_write PI m l v
    {{{ RET (); True }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hl & Hv) HΦ". wp_lam. wp_lam. wp_lam.
    wp_apply (locout_spec with "Hm"). iIntros (locout) "Hlocout".
      rewrite monP_triple.
    wp_apply ("Hlocout" $! l with "Hl"). iIntros (l2) "Hl2".
    wp_apply (pub_wrap_spec with "Hm"). iIntros (wrap) "Hwrap".
      rewrite monP_triple.
    wp_apply ("Hwrap" $! v with "Hv"). iIntros (v2) "Hv2".
    wp_apply (wp_store_low with "[Hm $Hl2 $Hv2]"); auto.
    by iDestruct "Hm" as (??) "(_&Hh&_&_)".
  Qed.

  Lemma shadow_read_spec γ m l :
    {{{ is_membrane γ m ∗ is_pub γ l }}} shadow_read PI m l
    ?{{{ v, RET v; on_val (is_pub γ) v }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hl) HΦ". wp_lam. wp_lam.
    wp_apply (pub_unwrap_spec with "Hm"). iIntros (f) "Hf".
    wp_apply (locout_spec with "Hm"). iIntros (locout) "Hlocout".
      rewrite (monP_pbit_mono noprogress progress) // 2!monP_triple.
    wp_apply ("Hlocout" $! l with "Hl"). iIntros (l2) "Hl2".
    wp_apply (wp_load_low with "[Hm $Hl2]")=>//;
      first by iDestruct "Hm" as (??) "(_&Hh&_&_)"; iFrame "Hh".
      iIntros (v2) "Hv2".
    wp_apply ("Hf" $! v2 with "Hv2"). iExact "HΦ".
  Qed.
End proof.

Definition pub_membrane `{heapG Σ, pubG Σ, LockImpl}
    (X : heap_extension Σ) (L : lock Σ) : pub Σ := {|
  intf.make_pub_spec := make_pub_spec X L;
  intf.pub_alloc_spec := pub_alloc_spec X;
  intf.pub_wrap_spec := pub_wrap_spec X;
  intf.pub_unwrap_spec := pub_unwrap_spec X;
  intf.shadow_read_spec := shadow_read_spec X;
  intf.shadow_write_spec := shadow_write_spec X
|}.
End proof.
