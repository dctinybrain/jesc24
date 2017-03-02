From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Export constructor.
From iris.heap_lang Require notation.
From iris.proofmode Require Import tactics.
Import uPred.

(* Minor annoyance: [solve_proper] can't handle our goals. *)
Local Notation ext R := (pointwise_relation _ R).

Ltac apply_eq :=
  lazymatch goal with
  | H : (eq ==> ext ?R)%signature ?f1 ?f2 |- ?R (?f1 ?x1 ?y1) (?f2 ?x1 ?y1)
    => apply H
  end.

Ltac solve_proper_eq :=
  preprocess_solve_proper;
  repeat (f_equiv; try (eassumption || apply_eq)).

(** * Reference monitors *)
(**
	The assertion [is_mon p e Ψ1 Ψ2] means that [e] is a
	reference monitor of "type" [Ψ1 → Ψ2] where [Ψ1] is a
	predicate on inputs of type [A ↣ val] and [Ψ2] relates inputs
	of type to outputs of type [B ↣ val].
*)
Section is_mon.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.
  Implicit Types v : val.
  Implicit Types e : expr.

  Definition is_monV (p : pbit) (v : val) (Ψ1 : A → iProp Σ)
      (Ψ2 : A → B → iProp Σ) : iProp Σ :=
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 a b }}})%I.

  Definition is_mon p e Ψ1 Ψ2 : iProp Σ := (
    □ ∀ p0 E0 Φ, (∀ v, is_monV p v Ψ1 Ψ2 -∗ Φ v) -∗ WP e @ p0; E0 {{ Φ }}
  )%I.

  Global Instance is_monV_persistent p v Ψ1 Ψ2 :
    PersistentP (is_monV p v Ψ1 Ψ2).
  Proof. apply _. Qed.

  Global Instance is_monV_ne p v n :
    Proper (ext (dist n) ==> ((=) ==> ext (dist n)) ==> dist n) (is_monV p v).
  Proof. solve_proper_eq. Qed.

  Global Instance is_monV_proper p v :
     Proper (ext (≡) ==> ((=) ==> ext (≡)) ==> (≡)) (is_monV p v).
  Proof. solve_proper_eq. Qed.

  Global Instance is_mon_persistent p e Ψ1 Ψ2 :
    PersistentP (is_mon p e Ψ1 Ψ2).
  Proof. apply _. Qed.

  Global Instance is_mon_ne p e n :
    Proper (ext (dist n) ==> ((=) ==> ext (dist n)) ==> dist n) (is_mon p e).
  Proof. solve_proper_eq. Qed.

  Global Instance is_mon_proper p e :
     Proper (ext (≡) ==> ((=) ==> ext (≡)) ==> (≡)) (is_mon p e).
  Proof. solve_proper_eq. Qed.

  Lemma monV_triple p v Ψ1 Ψ2 :
    is_monV p v Ψ1 Ψ2 ⊣⊢
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 a b }}}).
  Proof. by []. Qed.

  Lemma mon_triple p e Ψ1 Ψ2 :
    is_mon p e Ψ1 Ψ2 ⊣⊢
    □ ∀ p0 E0 Φ, (∀ v, is_monV p v Ψ1 Ψ2 -∗ Φ v) -∗ WP e @ p0; E0 {{ Φ }}.
  Proof. by []. Qed.

  Lemma mon_ret p v Ψ1 Ψ2 :
    is_monV p v Ψ1 Ψ2 ⊢ is_mon p v Ψ1 Ψ2.
  Proof.
    iIntros "#Hv !#". iIntros (p0 e0 Φ) "HΦ". rewrite -wp_value'.
    by iApply "HΦ".
  Qed.
End is_mon.
Typeclasses Opaque is_monV is_mon.

(** * Predicate-based reference monitors *)
(**
	This is just a special case of [is_mon] where [Ψ2] is a
	predicate on outputs rather than a relation on inputs and
	outputs.
*)
Section is_monP.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.
  Implicit Types v : val.
  Implicit Types e : expr.

  Definition is_monPV p v (Ψ1 : A → iProp Σ) (Ψ2 : B → iProp Σ) : iProp Σ :=
    is_monV p v Ψ1 (λ _, Ψ2).

  Definition is_monP p e (Ψ1 : A → iProp Σ) (Ψ2 : B → iProp Σ) : iProp Σ :=
    is_mon p e Ψ1 (λ _, Ψ2).

  Lemma monPV_triple p v Ψ1 Ψ2 :
    is_monPV p v Ψ1 Ψ2 ⊣⊢
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 b }}}).
  Proof. by []. Qed.

  Lemma monP_triple p e Ψ1 Ψ2 :
    is_monP p e Ψ1 Ψ2 ⊣⊢
    □ ∀ p0 E0 Φ, (∀ v, is_monPV p v Ψ1 Ψ2 -∗ Φ v) -∗ WP e @ p0; E0 {{ Φ }}.
  Proof. by []. Qed.

  Lemma monP_ret p v Ψ1 Ψ2 :
    is_monPV p v Ψ1 Ψ2 ⊢ is_monP p v Ψ1 Ψ2.
  Proof. exact: mon_ret. Qed.
End is_monP.
