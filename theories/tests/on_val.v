From iris.heap_lang Require Import heap.
From iris.proofmode Require Import tactics.

(* Test proofmode support for [on_val Ψ]. *)
Section tests.
  Context `{irisG heap_lang Σ} (Ψ : loc → iProp Σ).

  Goal ∀ v1 v2 P,       (* Using IntoAnd: Destructing pairs. *)
    (▷ on_val Ψ v1 -∗ ▷ on_val Ψ v2 -∗ P) -∗ on_val Ψ (PairV v1 v2) -∗ P.
  Proof.
    iIntros (v1 v2 P) "Hp (Hv1&Hv2)". by iApply ("Hp" with "Hv1 Hv2").
  Qed.

  Goal ∀ v1 v2 P,       (* Using FromSep: Combining pairs. *)
    (on_val Ψ (PairV v1 v2) -∗ P) -∗ ▷ on_val Ψ v1 -∗ ▷ on_val Ψ v2 -∗ P.
  Proof.
    iIntros (v1 v2 P) "Hp Hv1 Hv2". iCombine "Hv1" "Hv2" as "Hv".
    by iApply "Hp".
  Qed.

  Goal ∀ l P,   (* iAssumption, iExact use FromAssumption *)
    (Ψ l -∗ P) -∗ on_val Ψ (LocV l) -∗ P.
  Proof. iIntros (l P) "Hp Hlit". by iApply "Hp". Qed.

  Goal ∀ v P,   (* Using FromAssumption. *)
    (▷ on_val Ψ v -∗ P) -∗ on_val Ψ (InjLV v) -∗ P.
  Proof. iIntros (v P) "Hp Hv". by iApply "Hp". Qed.

  Goal ∀ v1 v2 P,       (* Using IntoLater: iNext simplifies the context *)
    (on_val Ψ v1 ∗ on_val Ψ v2 -∗ P) -∗ on_val Ψ (PairV v1 v2) -∗ ▷ P.
  Proof. iIntros (v1 v2 P) "Hp Hvi". iNext. by iApply "Hp". Qed.

  Goal ∀ v P,   (* Using IntoLater: iNext simplifies the context *)
    (on_val Ψ v -∗ P) -∗ on_val Ψ (InjLV v) -∗ ▷ P.
  Proof. iIntros (v P) "Hp Hv". iNext. by iApply "Hp". Qed.

  Goal ∀ l P,   (* FromAssumption, IntoLater *)
    (▷ Ψ l -∗ P) -∗ on_val Ψ (InjLV (LocV l)) -∗ P.
  Proof. iIntros (v P) "Hp Hv". iApply "Hp". by auto. Qed.

  Goal ∀ v P,   (* FromAssumption, IntoLater *)
    (▷ ▷ on_val Ψ v -∗ P) -∗ on_val Ψ (InjLV (InjRV v)) -∗ P.
  Proof. iIntros (v P) "Hp Hv". iApply "Hp". by auto. Qed.

  Goal ∀ v1 v2, (* Using FromLater: iNext simplifies the goal *)
    ▷ (on_val Ψ v1 ∗ on_val Ψ v2) -∗ on_val Ψ (PairV v1 v2).
  Proof. iIntros (v1 v2) "Hvi". iNext. done. Qed.

  Goal ∀ v,     (* Using FromLater: iNext simplifies the goal *)
    ▷ on_val Ψ v -∗ on_val Ψ (InjLV v).
  Proof. iIntros (v) "Hv". iNext. done. Qed.

  Goal ∀ v,     (* Using IsExcept0, except zero *)
    ◇ on_val Ψ (InjLV v) -∗ on_val Ψ (InjLV v).
  Proof. iIntros (v) "Hv". by iMod "Hv". Qed.

  Goal ∀ v P,   (* Using IsExcept0, timelessness *)
    TimelessP P →
    (P -∗ on_val Ψ (InjLV v)) -∗ ▷ P -∗ on_val Ψ (InjLV v).
  Proof. iIntros (v P ?) "Hp Hv". iMod "Hv". by iApply "Hp". Qed.
End tests.
