From iris.algebra Require Import auth gmap coPset.
From iris.heap_lang Require addenda.
From iris.heap_lang Require Import heap adequacy.
From iris.heap_lang.lib Require Import membrane abort assume lock.
From iris.heap_lang.lib Require spin_lock.
From iris.tests Require Import maps.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred addenda.algebra_auth.

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
Class PubImpl : Set := {
  make_pub : val; pub_ref : val; pub_wrap : val; pub_unwrap : val;
  shadow_read : val; shadow_write : val
}.
Arguments make_pub _ : clear implicits.
Arguments pub_ref _ : clear implicits.
Arguments pub_wrap _ : clear implicits.
Arguments pub_unwrap _ : clear implicits.
Arguments shadow_read _ : clear implicits.
Arguments shadow_write _ : clear implicits.

Section spec.
  Context `{heapG Σ} {PI : PubImpl}.
  Notation lowval := (low : val → iProp Σ).
  Implicit Types v f : val.

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
Arguments pub _ {_ _}.
Existing Instances is_membrane_persistent is_pub_timeless
  is_pub_persistent.

Section lemmas.
  Context `{heapG Σ, PI : PubImpl} (P : pub Σ).
  Implicit Types v : val.

  Lemma pub_wrap_val N γ m v1 :
    {{{ is_membrane P N γ m ∗ on_val (is_pub P γ) v1 }}}
      pub_wrap PI m v1
    {{{ v2, RET v2; low v2 }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hv1) HΦ".
    wp_apply (pub_wrap_spec with "Hm"). iIntros (w) "Hw".
      rewrite monP_triple.
    wp_apply ("Hw" with "* Hv1"). iExact "HΦ".
  Qed.

  Lemma pub_unwrap_val N γ m v2 :
    {{{ is_membrane P N γ m ∗ low v2 }}}
      pub_unwrap PI m v2
    ?{{{ v1, RET v1; on_val (is_pub P γ) v1 }}}.
  Proof.
    iIntros (Φ) "#(Hm & Hv2) HΦ".
    wp_apply (pub_unwrap_spec with "[$Hm $Hv2]"). iIntros (u) "Hu".
      rewrite monP_triple.
    wp_apply ("Hu" with "* Hv2"). iExact "HΦ".
  Qed.
End lemmas.
End intf.

(** * Public membrane clients *)

Definition max : val := λ: "a" "b", if: "a" ≤ "b" then "b" else "a".

Section mix.
  Context `{heapG Σ}.
  Implicit Types f g : val.
  Implicit Types n : Z.

  Definition is_mix (f : val) (F : Z → Z → Z) : iProp Σ :=
    (∀ n1 n2, {{{ True }}} f #n1 #n2 {{{ RET #(F n1 n2); True }}})%I.

  Lemma max_spec : is_mix max Z.max.
  Proof.
    iIntros (n1 n2) "!#". iIntros (Φ) "_ HΦ".
    wp_lam. wp_lam. wp_op=>?; wp_if.
    - rewrite Z.max_r //. by iApply "HΦ".
    - rewrite Z.max_l. by iApply "HΦ". exact: Z.lt_le_incl.
  Qed.
End mix.

(** ** Monotone counter with public limit *)

Module counter_1.
Section code.
  Context (LI : LockImpl) (PI : PubImpl).

  Definition get_limit : val := λ: "m" "r",
    let: "n1" := ! "r" in
    ifint: shadow_read PI "m" "r" as "n2" =>
      let: "n3" := max "n1" "n2" in
      let: <> := if: "n1" ≠ "n3" then "r" <- "n3" else () in
      "n3"
    else (shadow_write PI "m" "r" "n1" ;; "n1").

  Definition use : val := λ: "sync" "count" "limit" <>,
    "sync" (λ: <>,
      assert: (#0 ≤ ! "count");; assert: (! "count" ≤ ! "limit")
    ).
  Definition incr : val := λ: "m" "sync" "count" "limit" <>,
    "sync" (λ: <>,
      let: "n" := (! "count") + #1 in
      let: "b" := "n" ≤ get_limit "m" "limit" in
      let: <> := if: "b" then "count" <- "n" else () in
      "b"
    ).
  Definition make_counter : val := λ: "m",
    let: "count" := ref #0 in
    let: "limit" := pub_ref PI "m" #0 in
    let: "sync" := make_sync LI () in
    let: "use" := use "sync" "count" "limit" in
    let: "incr" := incr "m" "sync" "count" "limit" in
    let: "limit" := pub_wrap PI "m" "limit" in
    ("use", "limit", "incr").

  Definition client : expr :=
    let: "m" := make_pub PI () in
    make_counter "m".
End code.

Section proof.
  Context `{heapG Σ, LI : LockImpl, PI : PubImpl} (L : lock Σ) (P : pub Σ).
  Context (N : namespace).
  Let Nm : namespace := N .@ "pub".
  Let Nlk : namespace := N .@ "lk".
  Implicit Types f g : val.
  Implicit Types n : Z.

  Lemma get_limit_spec γ m l n1 :
    {{{ heap_ctx ∗ is_membrane P Nm γ m ∗ is_pub P γ l ∗ l ↦ #n1 }}}
      get_limit PI m l
    ?{{{ n2, RET #(Z.max n1 n2); l ↦ #(Z.max n1 n2) }}}.
  Proof.
    iIntros (Φ) "(#Hh & #Hm & #Hpub & Hl) HΦ". do 2!wp_lam.
      wp_load. wp_let.
    wp_apply (shadow_read_spec with "[$Hm $Hpub]"). iIntros (v2) "Hv2".
    wp_apply (wp_forget_progress progress).
    wp_typecast Hint; wp_match.
    - destruct (is_int_val _ Hint) as (n2&->). wp_finish.
      wp_apply (max_spec $! n1 n2 with "[]"); first done. iIntros "_". wp_let.
      wp_op=>[EQ|?]; wp_op; wp_if.
      + iApply "HΦ". by case: EQ=><-.
      + wp_store. by iApply "HΦ".
    - wp_apply (shadow_write_spec _ _ _ _ _ (#n1) with "[$Hm $Hpub]");
        first by simpl_on_val. iIntros "_". wp_seq.
      rewrite -{1 4}(Z.max_id n1). by iApply "HΦ".
  Qed.

  Definition counter_res (γ : name P) (c hi : loc) : iProp Σ :=
    (∃ n1 n2, c ↦ #n1 ∗ hi ↦ #n2 ∗ is_pub P γ hi ∗ ⌜0 ≤ n1 ≤ n2⌝)%I.

  Lemma use_spec sync γ c hi :
    {{{ heap_ctx ∗ is_sync sync (counter_res γ c hi) }}}
      use sync c hi
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hsync) HΦ". do 3!wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (? Φ) "_ HΦ". wp_finish. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (n1 n2) "(Hc & Hhi & #Hphi & %)".
    wp_apply wp_assert. wp_load. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext. wp_seq.
    wp_apply wp_assert. do 2!wp_load. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext.
    iApply ("HΨ" with "[Hc Hhi] [HΦ]").
    - iExists n1, n2. by iFrame "Hc Hhi Hphi".
    - iApply "HΦ". by simpl_low.
  Qed.

  Lemma incr_spec m γ sync c hi :
    {{{ heap_ctx ∗ is_membrane P Nm γ m ∗ is_sync sync (counter_res γ c hi) }}}
      incr PI m sync c hi
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hm & Hsync) HΦ". do 4!wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (? Φ) "_ HΦ". wp_finish. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (n1 n2) "(Hc & Hhi & #Hphi & %)".
      wp_load. wp_op. wp_let.
    wp_apply (get_limit_spec with "[$Hh $Hm $Hphi $Hhi]").
    iIntros (hi') "Hhi". wp_op=>?; wp_let; wp_if.
    - wp_store. iApply ("HΨ" with "[Hc Hhi]");
        last by iApply "HΦ"; simpl_low.
      iExists _, _. iFrame "Hc Hhi Hphi". iPureIntro. by lia.
    - iApply ("HΨ" with "[Hc Hhi]"); last by iApply "HΦ"; simpl_low.
      iExists _, _. iFrame "Hc Hhi Hphi". iPureIntro. by lia.
  Qed.

  Lemma make_counter_spec γ m :
    heapN ⊥ N →
    {{{ heap_ctx ∗ is_membrane P Nm γ m }}} make_counter LI PI m
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#(Hh & Hm) HΦ". wp_lam.
      wp_alloc c as "Hc". wp_let.
    wp_apply (pub_alloc_spec _ _ _ _ (#0) with "[$Hm]");
      first by simpl_on_val. iIntros (hi) "(#Hphi & Hhi)". wp_let.
    wp_apply (make_sync_spec L _ Nlk (counter_res γ c hi)
      with "[$Hh Hc Hhi]").
    - by solve_ndisj.
    - iExists 0, 0. by iFrame "Hc Hhi Hphi".
    iIntros (sync) "#Hsync". wp_let.
    wp_apply (use_spec with "[$Hh $Hsync]"). iIntros (use) "#Huse".
      wp_let.
    wp_apply (incr_spec with "[$Hh $Hm $Hsync]").
      iIntros (incr) "#Hincr". wp_let.
    wp_apply (pub_wrap_val _ _ _ _ (LocV hi) with "[$Hm Hphi]");
      first by simpl_on_val. iIntros (vhi) "#Hvhi". wp_let.
    iApply "HΦ". simpl_low. by iFrame "Huse Hvhi Hincr".
  Qed.

  Lemma client_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} client LI PI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/client.
    wp_apply (make_pub_spec P Nm with "Hh"); first by solve_ndisj.
      iIntros (m γ) "#Hm". wp_let.
    by wp_apply (make_counter_spec with "[$Hh $Hm]").
  Qed.
End proof.
End counter_1.

(** ** Counter with public upper and lower limits *)

Module counter_2.
Section code.
  Context (LI : LockImpl) (PI : PubImpl).

  Definition get_limit : val := λ: "m" "f" "r",
    let: "n1" := ! "r" in
    ifint: shadow_read PI "m" "r" as "n2" =>
      let: "n3" := "f" "n1" "n2" in
      let: <> := if: "n1" ≠ "n3" then "r" <- "n3" else () in
      let: <> := if: "n2" ≠ "n3" then shadow_write PI "m" "r" "n3" else () in
      "n3"
    else (shadow_write PI "m" "r" "n1" ;; "n1").

  Definition pick_lo : val := λ: "n" "lo1" "lo2",
    if: "lo2" ≤ "n" then "lo2" else "lo1".
  Definition pick_hi : val := λ: "n" "hi1" "hi2",
    if: "n" ≤ "hi2" then "hi2" else "hi1".
  Definition get_limits : val := λ: "m" "lo" "count" "hi" <>,
    let: "n" := ! "count" in
    let: "a" := get_limit "m" (pick_lo "n") "lo" in
    let: "b" := get_limit "m" (pick_hi "n") "hi" in
    ("a", "b").

  Definition use : val := λ: "sync" "lo" "count" "hi" <>,
    "sync" (λ: <>,
      assert: (! "lo" ≤ ! "count") ;; assert: (! "count" ≤ ! "hi")
    ).
  Definition decr : val := λ: "sync" "count" "f" <>,
    "sync" (λ: <>,
      let: "n" := (! "count") - #1 in
      let: "b" := Fst ("f" ()) ≤ "n" in
      let: <> := if: "b" then "count" <- "n" else () in
      "b"
    ).
  Definition incr : val := λ: "sync" "count" "f" <>,
    "sync" (λ: <>,
      let: "n" := (! "count") + #1 in
      let: "b" := "n" ≤ Snd ("f" ()) in
      let: <> := if: "b" then "count" <- "n" else () in
      "b"
    ).
  Definition make_counter : val := λ: "m",
    let: "lo" := pub_ref PI "m" #0 in
    let: "count" := ref #0 in
    let: "hi" := pub_ref PI "m" #0 in
    let: "sync" := make_sync LI () in
    let: "use" := use "sync" "lo" "count" "hi" in
    let: "get_limits" := get_limits "m" "lo" "count" "hi" in
    let: "decr" := decr "sync" "count" "get_limits" in
    let: "incr" := incr "sync" "count" "get_limits" in
    let: "lo" := pub_wrap PI "m" "lo" in
    let: "hi" := pub_wrap PI "m" "hi" in
    ("use", "lo", "hi", "incr", "decr").

  Definition client : expr :=
    let: "m" := make_pub PI () in
    make_counter "m".

  Definition client_12 : expr :=
    let: "m" := make_pub PI () in
    let: "c1" := counter_1.make_counter LI PI "m" in
    let: "c2" := make_counter "m" in
    ("c1", "c2").
End code.

Section proof.
  Context `{heapG Σ, LI : LockImpl, PI : PubImpl} (L : lock Σ) (P : pub Σ).
  Context (N : namespace).
  Let Nm : namespace := N .@ "pub".
  Let Nlk : namespace := N .@ "lk".
  Implicit Types f g : val.
  Implicit Types n : Z.

  Lemma get_limit_spec γ m :
    {{{ heap_ctx ∗ is_membrane P Nm γ m }}} get_limit PI m
    ?{{{ g, RET g; ∀ f F l n1,
      {{{ ⌜F n1 n1 = n1⌝ ∗ is_mix f F ∗ is_pub P γ l ∗ l ↦ #n1 }}} g f l
      ?{{{ n2, RET #(F n1 n2); l ↦ #(F n1 n2) }}}
    }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hm) HΦ". wp_lam.
    iApply "HΦ". clear Φ. iIntros (f F l n1) "!#".
      iIntros (Φ) "(HF & #Hf & #Hpub & Hl) HΦ". iDestruct "HF" as %HF.
      do 2!wp_lam. wp_load. wp_let.
    wp_apply (shadow_read_spec with "[$Hm $Hpub]"). iIntros (v2) "Hv2".
    wp_apply (wp_forget_progress progress).
    wp_typecast Hint; wp_match.
    - destruct (is_int_val _ Hint) as (n2&->). wp_finish.
      wp_apply ("Hf" $! n1 n2 with "[]"); first done. iIntros "_". wp_let.
      wp_op=>[EQ1|?]; wp_op; wp_if.
      + wp_op=>[EQ2|?]; wp_op; wp_if.
        * iApply "HΦ". by case: EQ1=><-.
        * wp_apply (shadow_write_spec _ _ _ _ _ (#(F n1 n2))
            with "[$Hm $Hpub]"); first by simpl_on_val. iIntros "_". wp_seq.
            case: EQ1=>EQ1. rewrite {1}EQ1.
          by iApply "HΦ".
      + wp_store. wp_op=>[EQ2|?]; wp_op; wp_if.
        * by iApply "HΦ".
        * wp_apply (shadow_write_spec _ _ _ _ _ (#(F n1 n2))
            with "[$Hm $Hpub]"); first by simpl_on_val. iIntros "_".
            wp_seq.
          by iApply "HΦ".
    - wp_apply (shadow_write_spec _ _ _ _ _ (#n1) with "[$Hm $Hpub]");
        first by simpl_on_val. iIntros "_". wp_seq.
      rewrite -{1 4}HF. by iApply "HΦ".
  Qed.

  Definition PickLo (n lo1 lo2 : Z) : Z :=
    if decide (lo2 ≤ n) then lo2 else lo1.
  Definition PickHi (n hi1 hi2 : Z) : Z :=
    if decide (n ≤ hi2) then hi2 else hi1.

  Lemma pick_lo_spec n :
    {{{ True }}} pick_lo #n ?{{{ f, RET f; is_mix f (PickLo n) }}}.
  Proof.
    iIntros (Φ) "HΦ". wp_lam. iApply "HΦ". clear Φ.
    iIntros (n1 n2) "!#". iIntros (Φ) "_ HΦ". do 2!wp_lam. rewrite/PickLo.
    wp_op=>?; wp_if.
    - case_decide. by iApply "HΦ". done.
    - case_decide. by exfalso; lia. by iApply "HΦ".
  Qed.

  Lemma pick_hi_spec n :
    {{{ True }}} pick_hi #n ?{{{ f, RET f; is_mix f (PickHi n) }}}.
  Proof.
    iIntros (Φ) "HΦ". wp_lam. iApply "HΦ". clear Φ.
    iIntros (n1 n2) "!#". iIntros (Φ) "_ HΦ". do 2!wp_lam. rewrite/PickHi.
    wp_op=>?; wp_if.
    - case_decide. by iApply "HΦ". done.
    - case_decide. by exfalso; lia. by iApply "HΦ".
  Qed.

  Definition is_get_limits (lo c hi : loc) (f : val) : iProp Σ := (
    ∀ n1 n n2, {{{ lo ↦ #n1 ∗ c ↦ #n ∗ hi ↦ #n2 ∗ ⌜n1 ≤ n ≤ n2⌝ }}} f ()
    ?{{{ n'1 n'2, RET (#(PickLo n n1 n'1), #(PickHi n n2 n'2));
      lo ↦ #(PickLo n n1 n'1) ∗ c ↦ #n ∗ hi ↦ #(PickHi n n2 n'2) }}}
  )%I.

  Lemma get_limits_spec γ m lo c hi :
    {{{ heap_ctx ∗ is_membrane P Nm γ m ∗ is_pub P γ lo ∗ is_pub P γ hi }}}
      get_limits PI m lo c hi
    {{{ f, RET f; is_get_limits lo c hi f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hm & Hplo & Hphi) HΦ". do 4!wp_lam.
    iApply "HΦ". clear Φ. iIntros (n1 n n2) "!#".
      iIntros (Φ) "(Hlo & Hc & Hhi & %) HΦ". wp_lam. wp_load. wp_let.
    wp_apply (get_limit_spec with "[$Hh $Hm]"). iIntros (g) "Hg".
    wp_apply pick_lo_spec. iIntros (f) "Hf".
    wp_apply ("Hg" $! f (PickLo n) lo n1 with "[$Hf $Hplo $Hlo]");
      first by rewrite/PickLo; iPureIntro; case_decide.
      clear f g. iIntros (n'1) "Hlo". wp_let.
    wp_apply (get_limit_spec with "[$Hh $Hm]"). iIntros (g) "Hg".
    wp_apply pick_hi_spec. iIntros (f) "Hf".
    wp_apply ("Hg" $! f (PickHi n) hi n2 with "[$Hf $Hphi $Hhi]");
      first by rewrite/PickHi; iPureIntro; case_decide.
      iIntros (n'2) "Hhi". wp_let.
    by iApply ("HΦ" with "[$Hlo $Hc $Hhi]").
  Qed.

  Definition counter_res (γ : name P) (lo c hi : loc) : iProp Σ := (
    ∃ n1 n n2, lo ↦ #n1 ∗ c ↦ # n ∗ hi ↦ #n2 ∗
    is_pub P γ lo ∗ is_pub P γ hi ∗ ⌜n1 ≤ n ≤ n2⌝
  )%I.

  Lemma use_spec sync γ lo c hi :
    {{{ heap_ctx ∗ is_sync sync (counter_res γ lo c hi) }}}
      use sync lo c hi
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hsync) HΦ". do 4!wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (? Φ) "_ HΦ". wp_finish. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (n1 n n2) "(Hlo & Hc & Hhi & #Hplo & #Hphi & %)".
    wp_apply wp_assert. do 2!wp_load. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext. wp_seq.
    wp_apply wp_assert. do 2!wp_load. wp_op=>?; last by exfalso; lia.
      iSplit; first done. iNext.
    iApply ("HΨ" with "[Hlo Hc Hhi] [HΦ]").
    - iExists n1, n, n2. by iFrame "Hlo Hc Hhi Hplo Hphi".
    - iApply "HΦ". by simpl_low.
  Qed.

  Lemma decr_spec sync γ lo c hi f :
    {{{ heap_ctx ∗ is_sync sync (counter_res γ lo c hi)
    ∗ is_get_limits lo c hi f }}}
      decr sync c f
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hsync & Hf) HΦ". do 3!wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (? Φ) "_ HΦ". wp_finish. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (n1 n n2) "(Hlo & Hc & Hhi & #Hplo & #Hphi & %)".
      wp_load. wp_op. wp_let. rewrite/is_get_limits.
    wp_apply ("Hf" $! n1 n n2 with "[$Hlo $Hc $Hhi]"); first done.
      iIntros (n'1 n'2) "(Hlo & Hc & Hhi)". wp_proj.
      wp_op=>?; wp_let; wp_if.
    - wp_store. iApply ("HΨ" with "[Hlo Hc Hhi] [HΦ]");
        last by iApply "HΦ"; simpl_low.
      iExists _, _, _. iFrame "Hlo Hc Hhi Hplo Hphi".
      iPureIntro. split. done. by rewrite/PickHi; case_decide; lia.
    - iApply ("HΨ" with "[Hlo Hc Hhi] [HΦ]");
        last by iApply "HΦ"; simpl_low.
      iExists _, _, _. iFrame "Hlo Hc Hhi Hplo Hphi".
      iPureIntro. split. by rewrite/PickLo; case_decide; lia.
      by rewrite/PickHi; case_decide; lia.
  Qed.

  Lemma incr_spec sync γ lo c hi f :
    {{{ heap_ctx ∗ is_sync sync (counter_res γ lo c hi)
    ∗ is_get_limits lo c hi f }}}
      incr sync c f
    {{{ f, RET f; low f }}}.
  Proof.
    iIntros (Φ) "#(Hh & Hsync & Hf) HΦ". do 3!wp_lam.
    iApply "HΦ". clear Φ. rewrite low_rec. iAlways. iNext.
      iIntros (? Φ) "_ HΦ". wp_finish. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync". iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (n1 n n2) "(Hlo & Hc & Hhi & #Hplo & #Hphi & %)".
      wp_load. wp_op. wp_let. rewrite/is_get_limits.
    wp_apply ("Hf" $! n1 n n2 with "[$Hlo $Hc $Hhi]"); first done.
      iIntros (n'1 n'2) "(Hlo & Hc & Hhi)". wp_proj.
      wp_op=>?; wp_let; wp_if.
    - wp_store. iApply ("HΨ" with "[Hlo Hc Hhi] [HΦ]");
        last by iApply "HΦ"; simpl_low.
      iExists _, _, _. iFrame "Hlo Hc Hhi Hplo Hphi".
      iPureIntro. split. by rewrite/PickLo; case_decide; lia. done.
    - iApply ("HΨ" with "[Hlo Hc Hhi] [HΦ]");
        last by iApply "HΦ"; simpl_low.
      iExists _, _, _. iFrame "Hlo Hc Hhi Hplo Hphi".
      iPureIntro. split. by rewrite/PickLo; case_decide; lia.
      by rewrite/PickHi; case_decide; lia.
  Qed.

  Lemma make_counter_spec γ m :
    heapN ⊥ N →
    {{{ heap_ctx ∗ is_membrane P Nm γ m }}} make_counter LI PI m
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#(Hh & Hm) HΦ". wp_lam.
    wp_apply (pub_alloc_spec _ _ _ _ (#0) with "[$Hm]");
      first by simpl_on_val. iIntros (lo) "(#Hplo & Hlo)". wp_let.
    wp_alloc c as "Hc". wp_let.
    wp_apply (pub_alloc_spec _ _ _ _ (#0) with "[$Hm]");
      first by simpl_on_val. iIntros (hi) "(#Hphi & Hhi)". wp_let.
    wp_apply (make_sync_spec L _ Nlk (counter_res γ lo c hi)
      with "[$Hh Hlo Hc Hhi]").
    - by solve_ndisj.
    - iExists 0, 0, 0. by iFrame "Hlo Hc Hhi Hplo Hphi".
    iIntros (sync) "#Hsync". wp_let.
    wp_apply (use_spec with "[$Hh $Hsync]"). iIntros (use) "#Huse".
      wp_let.
    wp_apply (get_limits_spec with "[$Hh $Hm $Hplo $Hphi]").
      iIntros (get) "#Hget". wp_let.
    wp_apply (decr_spec with "[$Hh $Hsync $Hget]").
      iIntros (decr) "#Hdecr". wp_let.
    wp_apply (incr_spec with "[$Hh $Hsync $Hget]").
      iIntros (incr) "#Hincr". wp_let.
    wp_apply (pub_wrap_val _ _ _ _ (LocV lo) with "[$Hm Hplo]");
      first by simpl_on_val. iIntros (vlo) "#Hvlo". wp_let.
    wp_apply (pub_wrap_val _ _ _ _ (LocV hi) with "[$Hm Hphi]");
      first by simpl_on_val. iIntros (vhi) "#Hvhi". wp_let.
    iApply "HΦ". simpl_low. by iFrame "Huse Hvlo Hvhi Hincr Hdecr".
  Qed.

  Lemma client_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} client LI PI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/client.
    wp_apply (make_pub_spec P Nm with "Hh"); first by solve_ndisj.
      iIntros (m γ) "#Hm". wp_let.
    by wp_apply (make_counter_spec with "[$Hh $Hm]").
  Qed.

  Lemma client_12_spec :
    heapN ⊥ N →
    {{{ heap_ctx }}} client_12 LI PI {{{ v, RET v; low v }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite/client_12.
    wp_apply (make_pub_spec P Nm with "Hh"); first by solve_ndisj.
      iIntros (m γ) "#Hm". wp_let.
    wp_apply (counter_1.make_counter_spec L P with "[$Hh $Hm]")=>//.
      iIntros (v1) "#Hv1". wp_let.
    wp_apply (make_counter_spec with "[$Hh $Hm]")=>//.
      iIntros (v2) "#Hv2". wp_let.
    iApply "HΦ". simpl_low. by iFrame "Hv1 Hv2".
  Qed.
End proof.
End counter_2.

(** * Public membrane implementation *)
(**
	We maintain a partial bijection between public locations and
	their shadows. The table grows during allocation and matters
	during wrapping and unwrapping.

	One can easily arrange for [locin], [unwrap], and
	[shadow_read] to make progress by (i) allocating a dummy
	public location in [make_pub] and (ii) having [locin] send
	unknown low locations to the dummy.
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
Class pubG Σ := PubG { pub_locsG : inG Σ (authR locset) }.
Definition pubΣ : gFunctors := #[ GFunctor (constRF (authR locset)) ].
(*
 * Lower priority than [heapG]'s instance of [authR locset] so that
 * [liveloc l] cannot incorrectly refer to our instance.
 *)
Existing Instance pub_locsG | 30.

Instance subG_pubΣ {Σ} : subG pubΣ Σ → pubG Σ.
Proof. intros [??]%subG_inv; constructor; apply _. Qed.

Section proof.
  Context `{heapG Σ, pubG Σ, LI : LockImpl} (L : lock Σ) (N : namespace).
  Let PI : PubImpl := code.pub_membrane LI.
  Implicit Types v f : val.

  (** Definitions *)

  Definition is_pub (γ : gname) (l : loc) : iProp Σ :=
    own γ (◯ (to_gset {[ l ]})).

  Definition pubhigh (γ : gname) (m1 : gmap loc val) : iProp Σ :=
    (own γ (● (dom (gset loc) m1)) ∗ live (dom _ m1))%I.

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
    pubhigh γ m1 -∗ liveloc l1 ==∗ pubhigh γ (<[l1:=l2]> m1).
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
      rewrite /pubhigh /publow /live dom_empty_L 2!big_sepS_empty.
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
    wp_apply (wp_alloc_live with "[$Hh $Ha]"); auto.
      iIntros (l1) "(Hl1&Hm1)". iDestruct "Hm1" as %Hm1.
      wp_let.
    wp_apply (wp_alloc_low_live _ _ _ _ (dom (gset loc) m2)
      with "[$Hh Hlo $Hv2]"); auto;
      first by iApply (big_sepS_mono' _ _ _ low_live with "Hlo").
      iIntros (l2) "(#Hl2&Hm2)". iDestruct "Hm2" as %Hm2.
      wp_let. wp_load. rewrite -> not_elem_of_dom in Hm1, Hm2.
    wp_apply (bij_insert_new_spec _ _ _ l1 l2 with "* [$Hbij]"); auto.
      iIntros (bij') "{Hbij} #Hbij". rewrite -wp_fupd. wp_store.
      iDestruct (mapsto_live with "Hl1") as "#Ha1".
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
    (L : lock Σ) : pub Σ := {|
  intf.make_pub_spec := make_pub_spec L;
  intf.pub_alloc_spec := pub_alloc_spec;
  intf.pub_wrap_spec := pub_wrap_spec;
  intf.pub_unwrap_spec := pub_unwrap_spec;
  intf.shadow_read_spec := shadow_read_spec;
  intf.shadow_write_spec := shadow_write_spec
|}.
End proof.

Section ClosedProofs.
  Import spin_lock.
  Let N : namespace := nroot .@ "example".
  Let Σ : gFunctors := #[ heapΣ; spin_lock.lockΣ; proof.pubΣ ].
  Let lock : LockImpl := spin.
  Let pub : PubImpl := code.pub_membrane lock.
  Let counter_1 : expr := counter_1.client lock pub.
  Let counter_2 : expr := counter_2.client lock pub.
  Let counter_12 : expr := counter_2.client_12 lock pub.

  Lemma counter_1_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C counter_1], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock. set P := proof.pub_membrane L.
    iApply (counter_1.client_spec L P N with "Hh"); auto with ndisj.
  Qed.

  Lemma counter_2_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C counter_2], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock. set P := proof.pub_membrane L.
    iApply (counter_2.client_spec L P N with "Hh"); auto with ndisj.
  Qed.

  Lemma counter_12_safe C t2 σ2 :
    AdvCtx C →
    rtc step ([ctx_fill C counter_12], good_state ∅) (t2, σ2) →
    is_good σ2.
  Proof.
    move=>??. eapply (robust_safety Σ); try done.
    { naive_solver eauto using is_closed_of_val. }
    iIntros (G) "Hh".
    set L := spin_lock. set P := proof.pub_membrane L.
    iApply (counter_2.client_12_spec L P N with "Hh"); auto with ndisj.
  Qed.
End ClosedProofs.

Print Assumptions counter_1_safe.
Print Assumptions counter_2_safe.
Print Assumptions counter_12_safe.
