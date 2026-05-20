From iris.heap_lang Require Export heap.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Import uPred.

(** * Lock interface *)

(** Operations *)
Class LockImpl : Set := { newlock' : val; acquire : val; release : val }.

Structure lock `{heapG Σ} {LI : LockImpl} := Lock {
  (** Predicates. Name ties [locked] to [is_lock]. *)
  name : Type;
  is_lock (γ: name) (lock: val) (R : iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (** Structure *)
  is_lock_ne γ lk n: Proper (dist n ==> dist n) (is_lock γ lk);
  is_lock_persistent γ lk R : PersistentP (is_lock γ lk R);
  locked_timeless γ : TimelessP (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (** Operations *)
  newlock'_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx }}} newlock' () @ p; ⊤
    {{{ lk γ, RET lk;  is_lock γ lk R ∗ locked γ }}};
  acquire_spec p γ lk R :
    {{{ is_lock γ lk R }}} acquire lk @ p; ⊤ {{{ RET (); locked γ ∗ R }}};
  release_spec p γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk @ p; ⊤ {{{ RET (); True }}}
}.
Arguments lock _ {_ _}.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper `{heapG Σ, LI : LockImpl} (L : lock Σ) lk R:
  Proper ((≡) ==> (≡)) (is_lock L lk R) := ne_proper _.

(** * Initially unlocked locks *)
Definition newlock {LI : LockImpl} : val := λ: <>,
  let: "lk" := newlock' () in release "lk" ;; "lk".

Section newlock.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ).

  Lemma newlock_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx ∗ R }}} newlock () @ p; ⊤
    {{{ lk γ, RET lk; is_lock L γ lk R }}}.
  Proof.
    iIntros (? Φ) "[#Hh Hr] HΦ". wp_lam.
    wp_apply (newlock'_spec L _ _ R with "[$Hh]"); first done.
      iIntros (lk γ) "[#Hlk Hl]". wp_let.
    wp_apply (release_spec with "[$Hlk $Hl $Hr]"). iIntros "_". wp_seq.
    by iApply ("HΦ" with "[$Hlk]").
  Qed.
End newlock.

(** * Synchronization *)
Section sync_code.
  Context {LI : LockImpl}.

  Definition sync_with : val := λ: "lk" "f",
    acquire "lk" ;; let: "r" := "f" () in release "lk" ;; "r".
  Definition make_sync : val := λ: <>,
    let: "lk" := newlock () in sync_with "lk".
End sync_code.

Section sync_proof.
  Context `{heapG Σ, LI : LockImpl} (L : lock Σ).

  Definition is_sync (sync : val) (R : iProp Σ) : iProp Σ := (
    □ ∀ p e Φ, ⌜Closed [] e⌝ -∗
    (∀ Ψ, R -∗ ▷ (∀ v, R -∗ Φ v -∗ Ψ v) -∗ WP e @ p; ⊤{{ Ψ }}) -∗
    WP sync (λ: <>, e) @ p; ⊤{{ Φ }}
  )%I.

  Global Instance is_sync_persistent v R : PersistentP (is_sync v R).
  Proof. apply _. Qed.

  Global Instance is_sync_ne n v : Proper (dist n ==> dist n) (is_sync v).
  Proof. solve_proper. Qed.

  Lemma sync_with_spec p γ lk (R : iProp Σ) :
    {{{ is_lock L γ lk R }}} sync_with lk @ p; ⊤
    {{{ sync, RET sync; is_sync sync R }}}.
  Proof.
    iIntros (Φ) "#Hlk HΦ". wp_lam.
    iApply "HΦ". iAlways. iIntros (p' e ψ) "% He". wp_let.
    wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked Hr]". wp_seq. wp_let.
    wp_apply ("He" with "[$Hr]"). iIntros (v) "Hr HΨ". wp_let.
    wp_apply (release_spec with "[$Hlk $Hlocked $Hr]"). iIntros "_".
      wp_seq. iExact "HΨ".
  Qed.

  Lemma make_sync_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx ∗ R }}} make_sync () @ p; ⊤
    {{{ sync, RET sync; is_sync sync R }}}.
  Proof.
    iIntros (? Φ) "[#Hh HR] HΦ". wp_lam.
    wp_apply (newlock_spec L _ _ R with "[$Hh $HR]"); first done.
      iIntros (lk γ) "Hlk". wp_let.
    by iApply (sync_with_spec with "[$Hlk] [$HΦ]").
  Qed.
End sync_proof.

Typeclasses Opaque is_sync.

Instance is_sync_proper Σ `{heapG Σ} sync :
  Proper ((≡) ==> (≡)) (is_sync sync) := ne_proper _.
