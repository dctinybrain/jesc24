From Coq Require Import Qcanon.
From iris.algebra Require Import excl.
From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Import assume lock.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Module Import caretaker.

(** * Caretaker interface *)
(**
	This is essentially a special case of the CAP-style lock
	interface [lock].
*)

(** Operations *)
Class CaretakerImpl : Set := {
  make_caretaker : val; wrap : val; disable : val; enable : val
}.
Arguments make_caretaker _ : clear implicits.
Arguments wrap _ : clear implicits.
Arguments disable _ : clear implicits.
Arguments enable _ : clear implicits.

Section caretaker.
  Context `{heapG Σ} {CI : CaretakerImpl}.

  Definition can_wrap (p : pbit) (f : val) (R : iProp Σ) : iProp Σ :=
    (∀ v : val, {{{ low v ∗ R }}} f v @ p; ⊤ {{{ v', RET v'; low v' ∗ R }}})%I.

  Structure caretaker := Caretaker {
    (** Predicates. Name ties [enabled] to [is_caretaker]. *)
    name : Type;
    is_caretaker (N : namespace) (γ : name) (ct : val) (R : iProp Σ) : iProp Σ;
    enabled (γ : name) (b : bool) : iProp Σ;
    (** Structure *)
    is_caretaker_ne N γ ct n : Proper (dist n ==> dist n) (is_caretaker N γ ct);
    is_caretaker_persistent N γ ct R : PersistentP (is_caretaker N γ ct R);
    enabled_timeless γ b : TimelessP (enabled γ b);
    enabled_exclusive γ b1 b2 : enabled γ b1 -∗ enabled γ b2 -∗ False;
    (** Operations *)
    make_caretaker_spec p N (R : iProp Σ) :
      heapN ⊥ N →
      {{{ heap_ctx }}} make_caretaker CI () @ p; ⊤
      {{{ ct γ, RET ct; is_caretaker N γ ct R ∗ enabled γ false }}};
    wrap_spec p N γ ct R (f : val) p1 :
      {{{ is_caretaker N γ ct R ∗ can_wrap p1 f R }}} wrap CI ct f @ p; ⊤
      {{{ v, RET v; low v }}};
    enable_spec p N γ ct R :
      {{{ is_caretaker N γ ct R ∗ enabled γ false ∗ R }}} enable CI ct @ p; ⊤
      {{{ RET (); enabled γ true }}};
    disable_spec p N γ ct R :
      {{{ is_caretaker N γ ct R ∗ enabled γ true }}} disable CI ct @ p; ⊤
      {{{ RET (); enabled γ false ∗ R }}}
  }.

  Global Instance can_wrap_persistent p f R :
    PersistentP (can_wrap p f R).
  Proof. apply _. Qed.

  Global Instance can_wrap_ne p f n :
    Proper (dist n ==> dist n) (can_wrap p f).
  Proof. solve_proper. Qed.

  Global Instance can_wrap_proper p f :
    Proper ((≡) ==> (≡)) (can_wrap p f) := ne_proper _.
End caretaker.
Typeclasses Opaque can_wrap.
Arguments caretaker _ {_ _}.

Existing Instances is_caretaker_ne is_caretaker_persistent
  enabled_timeless.

Instance is_caretaker_proper Σ `{heapG Σ, CaretakerImpl}
    (CT : caretaker Σ) N ct R :
  Proper ((≡) ==> (≡)) (is_caretaker CT N ct R) := ne_proper _.
End caretaker.

(** * Non-blocking caretaker *)
(**
	Wrappers fail unless the caretaker is enabled.
*)
Module nonblocking_caretaker.
Module impl.
  Definition make_caretaker (LI : LockImpl) : val := λ: <>,
    let: "enabled" := ref #false in
    let: "sync" := make_sync LI () in
    ("sync", "enabled").

  Definition wrap : val := λ: "ct" "f" "x",
    (Fst "ct") (λ: <>, assume: (! (Snd "ct")) ;; "f" "x").

  Definition enable : val := λ: "ct", (Fst "ct") (λ: <>, Snd "ct" <- #true).
  Definition disable : val := λ: "ct", (Fst "ct") (λ: <>, Snd "ct" <- #false).
End impl.

Definition nonblocking (LI : LockImpl) : CaretakerImpl := {|
  make_caretaker := impl.make_caretaker LI;
  wrap := impl.wrap;
  enable := impl.enable; disable := impl.disable
|}.

Section proof.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ).
  Context (p : pbit) (N : namespace).
  Let CI : CaretakerImpl := nonblocking LI.

  (** Definitions *)

  Let small := (1/3)%Qp.
  Let large := (small+small)%Qp.
  Lemma caretaker_split : (small + large = 1)%Qp.
  Proof. by apply Qp_eq; qc. Qed.

  Definition caretaker_res (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦{small} #b ∗ if b then R else True)%I.

  Definition is_caretaker (l : loc) (ct : val) (R : iProp Σ) : iProp Σ :=
    (∃ sync, ⌜heapN ⊥ N⌝ ∗ heap_ctx ∗ ⌜ct = (sync, l)%V⌝ ∗
     is_sync sync (caretaker_res l R))%I.

  Definition enabled (l : loc) (b : bool) : iProp Σ := (l ↦{large} #b)%I.

  (** Structure *)

  Global Instance caretaker_res_ne l n :
    Proper (dist n ==> dist n) (caretaker_res l).
  Proof. solve_proper. Qed.

  Global Instance is_caretaker_ne l ct n :
     Proper (dist n ==> dist n) (is_caretaker l ct).
  Proof. solve_proper. Qed.

  Global Instance is_caretaker_persistent l ct R :
    PersistentP (is_caretaker l ct R).
  Proof. apply _. Qed.

  Global Instance enabled_timeless l b : TimelessP (enabled l b).
  Proof. apply _. Qed.

  Lemma enabled_exclusive l b1 b2 : enabled l b1 -∗ enabled l b2 -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (mapsto_valid_2 with "[$H1 $H2]") as %Hv.
    by case: Hv.
  Qed.

  (** Operations *)

  Lemma make_caretaker_spec (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_caretaker CI () @ p; ⊤
    {{{ ct l, RET ct; is_caretaker l ct R ∗ enabled l false }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". wp_lam.
    wp_alloc l as "Hl". rewrite -caretaker_split.
      iDestruct "Hl" as "(Hsmall&Hlarge)". wp_let.
    set res := (caretaker_res l R)%I; iAssert res with "[Hsmall]" as "Hr";
      first by iExists false; iFrame.
    wp_apply (make_sync_spec L  _ _ res with "[$Hh $Hr]"); first done.
      iIntros (sync) "#Hsync". wp_let.
    iApply ("HΦ" $! _ l). iFrame. iExists sync. by iFrame "# %".
  Qed.

  Lemma wrap_spec l ct (R : iProp Σ) (f : val) p1 :
    {{{ is_caretaker l ct R ∗ can_wrap p1 f R }}} wrap CI ct f @ p; ⊤
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (Φ) "[Hct #Hf] HΦ".
      iDestruct "Hct" as (sync) "(%&#Hh&%&#Hsync)". subst.
      wp_lam. wp_let. iApply "HΦ". clear Φ.
    rewrite low_val. iAlways. iNext. iIntros (v) "#Hv". simpl_subst.
      wp_proj. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iClear "Hsync".
      iIntros (Ψ) "HR HΨ". iDestruct "HR" as (b) "(Hl&Hr)".
    wp_apply wp_assume. wp_proj. wp_load.
      iIntros "Hb". iDestruct "Hb" as %[= Hb]. subst. iNext. wp_seq.
      rewrite/can_wrap. setoid_rewrite always_elim.
      setoid_rewrite (wp_forget_progress p1 _ (f _)).
    wp_apply ("Hf" with "[$Hv $Hr]").
      iClear (v) "Hf Hv". iIntros (v) "(Hv&Hr)".
    iApply ("HΨ" with "[Hl Hr] Hv"). by iExists true; iFrame.
  Qed.

  Lemma enable_spec l ct (R : iProp Σ) :
    {{{ is_caretaker l ct R ∗ enabled l false ∗ R }}} enable CI ct @ p; ⊤
    {{{ RET (); enabled l true }}}.
  Proof.
    iIntros (Φ) "[Hct (Hlarge&Hr)] HΦ".
      iDestruct "Hct" as (sync) "(%&#Hh&%&#Hsync)". subst. wp_lam.
      wp_proj. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (b) "(Hsmall&_)".
    iDestruct (mapsto_agree with "[$Hlarge $Hsmall]") as %[=<-].
      iCombine "Hsmall" "Hlarge" as "Hl". rewrite caretaker_split.
    wp_proj. wp_store. rewrite -caretaker_split.
      iDestruct "Hl" as "(Hsmall&Hlarge)".
    iApply ("HΨ" with "[Hsmall Hr]"). by iExists true; iFrame. by iApply "HΦ".
  Qed.

  Lemma disable_spec l ct (R : iProp Σ) :
    {{{ is_caretaker l ct R ∗ enabled l true }}} disable CI ct @ p; ⊤
    {{{ RET (); enabled l false ∗ R }}}.
  Proof.
    iIntros (Φ) "[Hct Hlarge] HΦ".
      iDestruct "Hct" as (sync) "(%&#Hh&%&#Hsync)". subst. wp_lam.
      wp_proj. rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "HR HΨ".
      iDestruct "HR" as (b) "(Hsmall&Hr)".
    iDestruct (mapsto_agree with "[$Hlarge $Hsmall]") as %[=<-].
      iCombine "Hsmall" "Hlarge" as "Hl". rewrite caretaker_split.
    wp_proj. wp_store. rewrite -caretaker_split.
      iDestruct "Hl" as "(Hsmall&Hlarge)".
    iApply ("HΨ" with "[Hsmall]").
    by iExists false; iFrame. by iApply ("HΦ" with "[$Hlarge $Hr]").
  Qed.
End proof.
Typeclasses Opaque is_caretaker enabled.

Definition nonblocking_caretaker `{heapG Σ, LockImpl}
    (L : lock Σ) : caretaker Σ := {|
  caretaker.enabled_exclusive := enabled_exclusive;
  caretaker.make_caretaker_spec := make_caretaker_spec L;
  caretaker.wrap_spec := wrap_spec;
  caretaker.enable_spec := enable_spec;
  caretaker.disable_spec := disable_spec
|}.
End nonblocking_caretaker.

(** * Blocking caretaker *)
(**
	Wrappers block until the caretaker is enabled.
*)
Module blocking_caretaker.
Module impl.
Section impl.
  Context (LI : LockImpl).

  Definition make_caretaker : val := newlock' LI.
  Definition wrap : val := λ: "ct" "f" "x", sync_with LI "ct" (λ: <>, "f" "x").
  Definition enable : val := release LI.
  Definition disable : val := acquire LI.
End impl.
End impl.

Definition blocking (LI : LockImpl) : CaretakerImpl := {|
  make_caretaker := impl.make_caretaker LI;
  wrap := impl.wrap LI;
  enable := impl.enable LI; disable := impl.disable LI
|}.


(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class caretakerG Σ := CaretakerG { caretaker_tokG :> inG Σ (exclR unitC) }.
Definition caretakerΣ : gFunctors := #[GFunctor (constRF (exclR unitC))].

Instance subG_caretakerΣ {Σ} : subG caretakerΣ Σ → caretakerG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{heapG Σ, caretakerG Σ, LI : LockImpl} (L : lock Σ) (p : pbit)
    (N : namespace).
  Let CI : CaretakerImpl := blocking LI.

  (** Definitions *)
  Let name : Type := gname * lock.name L.

  Definition is_caretaker (γ : name) (ct : val) (R : iProp Σ) : iProp Σ :=
    is_lock L N (γ.2) ct R.

  Definition enabled (γ : name) (b : bool) : iProp Σ :=
    (own (γ.1) (Excl ()) ∗ (if b then True else locked L (γ.2)))%I.

  (** Structure *)

  Global Instance is_caretaker_ne γ ct n :
    Proper (dist n ==> dist n) (is_caretaker γ ct).
  Proof. solve_proper. Qed.

  Global Instance is_caretaker_persistent γ ct R :
    PersistentP (is_caretaker γ ct R).
  Proof. apply _. Qed.

  Global Instance enabled_timeless γ b : TimelessP (enabled γ b).
  Proof. case: b; apply _. Qed.

  Lemma enabled_exclusive γ b1 b2 : enabled γ b1 -∗ enabled γ b2 -∗ False.
  Proof.
    iIntros "(H1&_) (H2&_)". by iDestruct (own_valid_2 with "H1 H2") as %?.
  Qed.

  (** Operations *)

  Lemma make_caretaker_spec (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx }}} make_caretaker CI () @ p; ⊤
    {{{ ct γ, RET ct; is_caretaker γ ct R ∗ enabled γ false }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite -wp_fupd /make_caretaker.
    iApply (newlock'_spec _ _ _ _ R with "Hh"); first done.
      iNext. iIntros (lk γlk) "(#Hlk & Hlocked)".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done. iModIntro.
    iApply ("HΦ" $! lk (γ, γlk)). iSplitR. done. by iFrame.
  Qed.

  Lemma wrap_spec γ ct (R : iProp Σ) (f : val) p1 :
    {{{ is_caretaker γ ct R ∗ can_wrap p1 f R }}} wrap CI ct f @ p; ⊤
    {{{ v, RET v; low v }}}.
  Proof.
    iIntros (Φ) "#(Hct & Hf) HΦ". wp_lam. wp_lam.
    iApply "HΦ". clear Φ. rewrite low_val. iAlways. iNext.
      iIntros (v) "Hv". simpl_subst.
    wp_apply (sync_with_spec with "Hct"). iIntros (sync) "#Hsync".
      rewrite/is_sync.
    wp_apply ("Hsync" with "[%]"). iIntros (Ψ) "Hr HΨ".
      rewrite/can_wrap. setoid_rewrite always_elim.
      setoid_rewrite (wp_forget_progress p1 _ (f _)).
    wp_apply ("Hf" with "[$Hv $Hr]"). clear v. iIntros (v) "[Hv Hr]".
    by iApply ("HΨ" with "Hr Hv").
  Qed.

  Lemma enable_spec γ ct (R : iProp Σ) :
    {{{ is_caretaker γ ct R ∗ enabled γ false ∗ R }}} enable CI ct @ p; ⊤
    {{{ RET (); enabled γ true }}}.
  Proof.
    iIntros (Φ) "(Hct & (Htok & Hlock) & Hr) HΦ". rewrite/enable.
    wp_apply (release_spec with "[$Hct $Hlock $Hr]"). rewrite wand_True.
    by iApply ("HΦ" with "[$Htok]").
  Qed.

  Lemma disable_spec γ ct (R : iProp Σ) :
    {{{ is_caretaker γ ct R ∗ enabled γ true }}} disable CI ct @ p; ⊤
    {{{ RET (); enabled γ false ∗ R }}}.
  Proof.
    iIntros (Φ) "(Hct & (Htok & Hlock)) HΦ". rewrite/disable.
    wp_apply (acquire_spec with "[$Hct $Hlock]"). iIntros "(Hlock & Hr)".
    by iApply ("HΦ" with "[$Htok $Hlock $Hr]").
  Qed.
End proof.
Typeclasses Opaque is_caretaker enabled.

Definition blocking_caretaker `{heapG Σ, caretakerG Σ, LockImpl}
    (L : lock Σ) : caretaker Σ := {|
  caretaker.enabled_exclusive := enabled_exclusive L;
  caretaker.make_caretaker_spec := make_caretaker_spec L;
  caretaker.wrap_spec := wrap_spec L;
  caretaker.enable_spec := enable_spec L;
  caretaker.disable_spec := disable_spec L
|}.
End blocking_caretaker.
