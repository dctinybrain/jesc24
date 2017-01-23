From iris.heap_lang Require Export heap notation.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Import tactics.
Import uPred.

(** * Lock interface *)
Structure lock Σ `{!heapG Σ} := Lock {
  (* -- operations -- *)
  newlock' : val;
  acquire : val;
  release : val;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  name : Type;
  is_lock (N: namespace) (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (* -- general properties -- *)
  is_lock_ne N γ lk n: Proper (dist n ==> dist n) (is_lock N γ lk);
  is_lock_persistent N γ lk R : PersistentP (is_lock N γ lk R);
  locked_timeless γ : TimelessP (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (* -- operation specs -- *)
  newlock'_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx }}} newlock' #() @ p; ⊤
    {{{ lk γ, RET lk;  is_lock N γ lk R ∗ locked γ }}};
  acquire_spec p N γ lk R :
    {{{ is_lock N γ lk R }}} acquire lk @ p; ⊤ {{{ RET #(); locked γ ∗ R }}};
  release_spec p N γ lk R :
    {{{ is_lock N γ lk R ∗ locked γ ∗ R }}} release lk @ p; ⊤ {{{ RET #(); True }}}
}.

Arguments newlock' {_ _} _.
Arguments acquire {_ _} _.
Arguments release {_ _} _.
Arguments is_lock {_ _} _ _ _ _ _.
Arguments locked {_ _} _ _.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper Σ `{!heapG Σ} (L: lock Σ) N lk R:
  Proper ((≡) ==> (≡)) (is_lock L N lk R) := ne_proper _.

(** * The [newlock] function *)
Section newlock.
  Context `{heapG Σ} (L : lock Σ).

  Definition newlock : val := λ: <>,
    let: "lk" := newlock' L #() in release L "lk" ;; "lk".

  Lemma newlock_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx ∗ R }}} newlock #() @ p; ⊤
    {{{ lk γ, RET lk; is_lock L N γ lk R }}}.
  Proof.
    iIntros (? Φ) "[#Hh Hr] HΦ"; wp_lam.
    wp_bind (newlock' _ _); iApply (newlock'_spec _ _ _ _ R with "[$Hh]");
      first done; iNext; iIntros (lk γ) "[#Hlk Hl]"; wp_let.
    wp_bind (release _ _); iApply (release_spec with "[$Hlk $Hl $Hr]"); iNext;
      iIntros "_"; wp_seq.
    by iApply ("HΦ" with "[$Hlk]").
  Qed.
End newlock.

(** * The [sync_with] and [make_sync] functions *)
Section sync.
  Context `{heapG Σ} (L : lock Σ).

  Definition sync_with : val := λ: "lk" "f",
    acquire L "lk" ;; let: "r" := "f" #() in release L "lk" ;; "r".
  Definition make_sync : val := λ: <>,
    let: "lk" := newlock L #() in sync_with "lk".

  Definition is_sync (sync : val) (R : iProp Σ) : iProp Σ := (
    □ ∀ p e Φ, ⌜Closed [] e⌝ -∗
    (∀ Ψ, R -∗ ▷ (∀ v, R -∗ Φ v -∗ Ψ v) -∗ WP e @ p; ⊤{{ Ψ }}) -∗
    WP sync (λ: <>, e) @ p; ⊤{{ Φ }}
  )%I.

  Global Instance is_sync_persistent v R : PersistentP (is_sync v R).
  Proof. apply _. Qed.

  Global Instance is_sync_ne n v : Proper (dist n ==> dist n) (is_sync v).
  Proof. solve_proper. Qed.

  Lemma sync_with_spec p N γ lk (R : iProp Σ) :
    {{{ is_lock L N γ lk R }}} sync_with lk @ p; ⊤
    {{{ sync, RET sync; is_sync sync R }}}.
  Proof.
    iIntros (Φ) "#Hlk HΦ". wp_lam.
    iApply "HΦ". iAlways. iIntros (p' e ψ) "% He". wp_let.
    wp_bind (acquire _ _). iApply (acquire_spec with "Hlk"). iNext.
      iIntros "[Hlocked Hr]". wp_seq. wp_let.
    iApply ("He" with "[$Hr]"). iNext. iIntros (v) "Hr HΨ". wp_let.
    wp_bind (release _ _). iApply (release_spec with "[$Hlk $Hlocked $Hr]").
      iNext. rewrite wand_True. wp_seq. iExact "HΨ".
  Qed.

  Lemma make_sync_spec p N (R : iProp Σ) :
    heapN ⊥ N →
    {{{ heap_ctx ∗ R }}} make_sync #() @ p; ⊤
    {{{ sync, RET sync; is_sync sync R }}}.
  Proof.
    iIntros (? Φ) "[#Hh HR] HΦ"; wp_lam.
    wp_bind (newlock _ _);
      iApply (newlock_spec _ _ _ R with "[$Hh $HR]"); first done;
      iNext; iIntros (lk γ) "#Hlk"; wp_let.
    by iApply (sync_with_spec with "[$Hlk] [$HΦ]").
  Qed.
End sync.

Typeclasses Opaque is_sync.
Instance: Params (@is_sync) 2.

Instance is_sync_proper Σ `{heapG Σ} sync :
  Proper ((≡) ==> (≡)) (is_sync sync) := ne_proper _.
