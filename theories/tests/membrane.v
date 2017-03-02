From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import membrane abort lock.
From iris.tests Require Import maps.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

(* PDS: Neither LockImpl nor CaretakerImpl should be type classes. *)
(* PDS: Heap should actually define [lowval]. *)

(** * Public membrane interface *)
(**
	As a matter of policy, we use [pub_ref] to "declare" _public
	locations_. Public locations work like high-integrity
	locations with one twist: Each has a unique, low-integrity
	_shadow location_ serving as its proxy for use in adversarial
	code.

	Public locations lift as _public values_. The function
	[pub_wrap] converts a public value to its low-integrity
	counterpart (by replacing public locations with their
	shadows). Its dual is [pub_unwrap].

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
    shadow_read : val;
    shadow_write : val;
    pub_wrap : val;
    pub_unwrap : val
  }.

  Section spec.
    Context `{heapG Σ} {PI : PubImpl}.
    Notation lowval := (low : val → iProp Σ).

    Structure pub := Pub {
      (** Predicates *)
      (** Name is used to associate [publoc] with [is_membrane]. *)
      name : Type;
      is_membrane (N : namespace) (γ : name) (m : val) : iProp Σ;
      publoc (γ : name) (l : loc) : iProp Σ;
      (** Structure *)
      is_membrane_persistent N γ m : PersistentP (is_membrane N γ m);
      publoc_persistent γ l : PersistentP (publoc γ l);
      publoc_timeless γ l : TimelessP (publoc γ l);
      (** Operations *)
      make_pub_spec N :
        heapN ⊥ N →
        {{{ heap_ctx }}} make_pub PI () {{{ m γ, RET m; is_membrane N γ m }}};
      pub_alloc_spec N γ m (v : val) :
        {{{ is_membrane N γ m ∗ on_val (publoc γ) v }}} pub_ref PI m v
        {{{ l, RET LocV l; publoc γ l ∗ l ↦ v }}};
      pub_wrap_spec N γ m v1 :
        {{{ is_membrane N γ m ∗ on_val (publoc γ) v1 }}} pub_wrap PI m v1
        {{{ v2, RET v2; low v2 }}};
      pub_unwrap_spec N γ m v2 :
        {{{ is_membrane N γ m ∗ lowval v2 }}} pub_unwrap PI m v2
        ?{{{ v1, RET v1; on_val (publoc γ) v1 }}};
      shadow_read_spec N γ m l :
        {{{ is_membrane N γ m ∗ publoc γ l }}} shadow_read PI m l
        {{{ v, RET v; on_val (publoc γ) v }}};
      shadow_write_spec N γ m l v :
        {{{ is_membrane N γ m ∗ publoc γ l ∗ on_val (publoc γ) v }}}
          shadow_write PI m l v
        {{{ RET (); True }}}
    }.
  End spec.
  Arguments pub _ {_ _}.
  Existing Instances is_membrane_persistent publoc_persistent
    publoc_timeless.
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
  Definition pub_ref : val := λ: "m" "x",
    let: "r1" := ref "x" in
    let: "r2" := ref (pub_wrap "m" "x") in
    let: "sync" := Fst "m" in let: "tbl" := Snd "m" in
    "sync" (λ: <>, "tbl" <- bij_insert_new (! "tbl") "r1" "r2") ;;
    "r1".
  Definition shadow_read : val := λ: "m" "l",
    pub_unwrap "m" (! locout "m" "l").
  Definition shadow_write : val := λ: "m" "l" "x",
    locout "m" "l" <- pub_wrap "m" "x".
End pub_code.

(** The CMRA we need. *)
(*
	PDS: We should have defined [CoInductive loc := Loc of positive]
	so that we can write simply [gsetUR loc] here rather
	than [coPsetUR].
*)
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

From iris.algebra Require Import coPset auth.	(* PDS: Hoist. *)

Notation locset := coPsetUR.	(* PDS: Should be [gsetUR loc]. *)
Class pubG Σ := PubG {
  pub_locsetG :> inG Σ (authR locset)
}.
Definition pubΣ : gFunctors := #[GFunctor (constRF (authR locset))].

Instance subG_pubΣ {Σ} : subG pubΣ Σ → pubG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section pub_proof.
  Context `{heapG Σ, pubG Σ, LI : LockImpl} (L : lock Σ).
  Context (N : namespace).

  Definition publoc (γ : gname) (l : loc) : iProp Σ := own γ (◯ ({[ l ]})).
  Definition pubhigh (γ : gname) (m1 : gmap loc val) : iProp Σ :=
    own γ (● (dom _ m1)).
  Definition publow (m2 : gmap loc val) : iProp Σ :=
    ([∗ map] l2↦_ ∈ m2, low l2)%I.

  Definition tbl_res (t : loc) (γ : gname) : iProp Σ := (
    ∃ bij m1 m2, t ↦ bij ∗ ⌜is_bij bij m1 m2⌝ ∗
    pubhigh γ m1 ∗ publow m2
  )%I.

  Definition is_membrane (γ : gname) (m : val) : iProp Σ := (
    ∃ (t : loc) sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜m = (sync, t)%V⌝ ∗
    is_sync sync (tbl_res t γ)
  )%I.

  (** Structure *)
  Global Instance is_membrane_persistent γ m :
    PersistentP (is_membrane γ m).
  Proof. apply _. Qed.
  Global Instance publoc_persistent γ l : PersistentP (publoc γ l).
  Proof. apply _. Qed.
  Global Instance publoc_timeless γ l : TimelessP (publoc γ l).
  Proof. apply _. Qed.

  Lemma publoc_obs γ m1 l1 :
    is_Some (m1 !! l1) →
    pubhigh γ m1 ==∗ pubhigh γ m1 ∗ publoc γ l1.
  Proof.
    move=>?. rewrite -own_op. apply own_update.
    apply auth_frag_alloc; try apply _.
    by apply coPset_included, elem_of_subseteq_singleton, elem_of_dom.
  Qed.

  (** Operations *)
  Lemma make_pub_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_pub () {{{ m γ, RET m; is_membrane γ m }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam. wp_alloc t as "Ht". wp_let.
      rewrite -wp_fupd.
    iMod (own_alloc (Auth (Excl' ∅) ∅)) as (γ) "Hγ"; first done.
    wp_apply (make_sync_spec L _ _ (tbl_res t γ) with "[$Hh Ht Hγ]").
    - solve_ndisj.
    - iExists bij_empty, ∅, ∅.
      rewrite /pubhigh dom_empty /publow big_sepM_empty.
      iFrame "Ht Hγ". iPureIntro. exact: bij_empty_spec.
    iIntros (sync) "#Hsync". wp_let. iModIntro.
    iApply ("HΦ" $! _ γ). iExists t, sync. by iFrame "% Hh Hsync".
  Qed.

  Lemma locout_spec p E γ m :
    {{{ is_membrane γ m }}} locout m @ p; E
    {{{ v, RET v; is_monPV progress v (publoc γ) low }}}.
  Proof.
    iIntros (Φ) "#Hm HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (l1) "!#". iIntros (Φ) "Hl1 HΦ".
      wp_lam.
    iDestruct "Hm" as (t sync) "(% & Hh & % & Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & Hhi & #Hlo)". wp_load.
    iDestruct (own_valid_2 with "Hhi Hl1") as %
      [(v1&?)%coPset_included%elem_of_subseteq_singleton
       %elem_of_dom ?]%auth_valid_discrete_2.
    wp_apply (bij_lookup_partial_Some_spec _ _ _ _ _ l1 with "Hbij")=>//.
      iIntros (l2) "[%%]". subst.
      iDestruct (big_sepM_lookup _ _ l2 with "Hlo") as "Hl2"=>//.
    iApply ("HΨ" with "[Ht Hhi]").
    - iExists bij, m1, m2. by iFrame "Ht Hbij Hhi Hlo".
    by iApply ("HΦ" with "Hl2").
  Qed.

  Lemma locout_mon γ m :
    is_membrane γ m -∗ is_monP progress (locout m) (publoc γ) low.
  Proof.
    iIntros "#Hm". rewrite monP_triple. iAlways. iIntros (p0 E0 Φ) "HΦ".
    wp_apply (locout_spec with "Hm"). iIntros (vout) "Hout".
    by iApply ("HΦ" with "Hout").
  Qed.

  Lemma locin_spec p E γ m :
    {{{ is_membrane γ m }}} locin m @ p; E
    {{{ v, RET v; is_monPV noprogress v low (publoc γ) }}}.
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
    iMod (publoc_obs _ _ l1 with "Hhi") as "[Hhi Hl1]"; first by exists l2.
    iApply ("HΨ" with "[Ht Hhi]").
    - iExists bij, m1, m2. by iFrame "Ht Hbij Hhi Hlo".
    by iApply ("HΦ" with "Hl1").
  Qed.

  Lemma locin_mon γ m :
    is_membrane γ m -∗ is_monP noprogress (locin m) low (publoc γ).
  Proof.
    iIntros "#Hm". rewrite monP_triple. iAlways. iIntros (p0 E0 Φ) "HΦ".
    wp_apply (locin_spec with "Hm"). iExact "HΦ".
  Qed.

  Lemma pub_wrap_spec γ m v1 :
    {{{ is_membrane γ m ∗ on_val (publoc γ) v1 }}} pub_wrap m v1
    {{{ v2, RET v2; low v2 }}}.
  Proof.
    iIntros (Φ) "(#Hm & Hv1) HΦ". wp_lam.
    wp_apply (membrane_spec _ _ progress _ (publoc γ) low with "[]").
    - by iApply (locout_mon with "Hm").
    iIntros (w) "Hw".
    wp_apply ("Hw" $! _ _ noprogress with "* []").
    - by iApply (locin_mon with "Hm").
    iIntros (wrap) "Hwrap". rewrite monPV_triple.
    wp_apply ("Hwrap" with "* Hv1"). iExact "HΦ".
  Qed.

  Lemma pub_unwrap_spec γ m (v2 : val) :
    {{{ is_membrane γ m ∗ low v2 }}} pub_unwrap m v2
    ?{{{ v1, RET v1; on_val (publoc γ) v1 }}}.
  Proof.
    iIntros (Φ) "(#Hm & Hv2) HΦ". wp_lam.
    wp_apply (membrane_spec _ _ noprogress _ low (publoc γ) with "[]").
    - by iApply (locin_mon with "Hm").
    iIntros (u) "Hu".
    wp_apply ("Hu" $! _ _ progress with "* []").
    - by iApply (locout_mon with "Hm").
    iIntros (unwrap) "Hunwrap". rewrite monPV_triple.
    wp_apply ("Hunwrap" with "* Hv2"). iExact "HΦ".
  Qed.

  Lemma membrane_heap γ m : is_membrane γ m -∗ heap_ctx.
  Proof.
    iIntros "Hm". iDestruct "Hm" as (??) "(_&Hh&_&_)". by iFrame "Hh".
  Qed.

  Lemma pub_alloc_spec γ m (v : val) :
    {{{ is_membrane γ m ∗ on_val (publoc γ) v }}} pub_ref m v
    {{{ l, RET LocV l; publoc γ l ∗ l ↦ v }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hv) HΦ". wp_lam. wp_lam.
    iDestruct (membrane_heap with "Hm") as "Hh".
      wp_alloc l1 as "Hl1". wp_let.
    wp_apply (pub_wrap_spec with "[$Hm $Hv]"). iIntros (v2) "Hv2".
      wp_apply (wp_alloc_low with "[$Hh $Hv2]"); auto.
      iIntros (l2) "Hl2". wp_let.
    iDestruct "Hm" as (t sync) "(%&_&%&Hsync)". subst.
      do 2!(wp_proj; wp_let). rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (bij m1 m2) "(Ht & #Hbij & Hhi & #Hlo)". wp_load.
    wp_apply (bij_insert_new_spec _ _ _ l1 l2 with "* [$Hbij]"); last first.
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
