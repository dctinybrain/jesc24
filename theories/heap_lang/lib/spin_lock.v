From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl.
From iris.heap_lang.lib Require Import lock.

Module impl.
Definition newlock' : val := λ: <>, ref #true.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then () else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.
End impl.

Instance code : LockImpl := {|
  newlock' := impl.newlock'; acquire := impl.acquire;
  release := impl.release
|}.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (constRF (exclR unitC))].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ}.

  Record name : Type := { nsp : namespace; tok : gname; loc : loc }.

  Definition lock_inv (γ : name) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, loc γ ↦ #b ∗ if b then True else own (tok γ) (Excl ()) ∗ R)%I.

  Definition is_lock (γ : name) (lk : val) (R : iProp Σ) : iProp Σ :=
    (⌜heapN ⊥ (nsp γ)⌝ ∧ heap_ctx ∧ ⌜lk = loc γ⌝ ∧
     inv (nsp γ) (lock_inv γ R))%I.

  Definition locked (γ : name): iProp Σ := own (tok γ) (Excl ()).

  Lemma locked_exclusive (γ : name) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne n γ : Proper (dist n ==> dist n) (lock_inv γ).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ lk n : Proper (dist n ==> dist n) (is_lock γ lk).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ lk R : PersistentP (is_lock γ lk R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma newlock'_spec p N (R : iProp Σ):
    heapN ⊥ N →
    {{{ heap_ctx }}} newlock' () @ p; ⊤
    {{{ lk γ, RET lk; is_lock γ lk R ∗ locked γ }}}.
  Proof.
    iIntros (? Φ) "#Hh HΦ". rewrite -wp_fupd.
    wp_seq. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γtok) "Hγ"; first done.
    set γ := {| nsp := N; tok := γtok; loc := l |}.
    iMod (inv_alloc N _ (lock_inv γ R) with "[Hl]") as "#?".
    { iIntros "!>". iExists true. by iFrame. }
    iModIntro. iApply ("HΦ" $! _ γ).
    iSplitR "Hγ". rewrite/is_lock. by eauto. by iFrame.
  Qed.

  Lemma try_acquire_spec p γ lk R :
    {{{ is_lock γ lk R }}} impl.try_acquire lk @ p; ⊤
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as "(% & #? & % & #?)"; subst.
    wp_rec. iInv (nsp γ) as ([]) "[Hl HR]" "Hclose".
    - wp_cas_fail. iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iApply ("HΦ" $! false). done.
    - wp_cas_suc. iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.

  Lemma acquire_spec p γ lk R :
    {{{ is_lock γ lk R }}} acquire lk @ p; ⊤ {{{ RET (); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec p γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk @ p; ⊤
    {{{ RET (); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as "(% & #? & % & #?)"; subst.
    wp_let. iInv (nsp γ) as (b) "[Hl _]" "Hclose".
    wp_store. iApply "HΦ". iApply "Hclose". iNext. iExists false. by iFrame.
  Qed.
End proof.

Typeclasses Opaque is_lock locked.

Definition proof `{!heapG Σ, !lockG Σ} : lock Σ :=
  {| lock.locked_exclusive := locked_exclusive; lock.newlock'_spec := newlock'_spec;
     lock.acquire_spec := acquire_spec; lock.release_spec := release_spec |}.
