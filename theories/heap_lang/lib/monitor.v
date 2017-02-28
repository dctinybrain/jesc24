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
	The assertion [is_mon p v R Ψ1 Ψ2] means that [v] is a
	reference monitor (with progress bit [p]) of "type" [Ψ1 → Ψ2]
	where [Ψ1] is a predicate on inputs of type [A] and [Ψ2]
	relates inputs of type [A] to outputs of type [B]. Both [A]
	and [B] must have [constructor] instances.
*)
Section is_mon.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.

  Definition is_mon (p : pbit) (v : val) (Ψ1 : A → iProp Σ)
      (Ψ2 : A → B → iProp Σ) : iProp Σ :=
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 a b }}})%I.

  Global Instance is_mon_persistent p v Ψ1 Ψ2 :
    PersistentP (is_mon p v Ψ1 Ψ2).
  Proof. apply _. Qed.

  Global Instance is_mon_ne p v n :
    Proper (ext (dist n) ==> ((=) ==> ext (dist n)) ==> dist n) (is_mon p v).
  Proof. solve_proper_eq. Qed.

  Global Instance is_mon_proper p v :
     Proper (ext (≡) ==> ((=) ==> ext (≡)) ==> (≡)) (is_mon p v).
  Proof. solve_proper_eq. Qed.

  Lemma mon_triple p v Ψ1 Ψ2 :
    is_mon p v Ψ1 Ψ2 ⊣⊢
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 a b }}})%I.
  Proof. by []. Qed.
End is_mon.
Typeclasses Opaque is_mon.

(** * Predicate-based reference monitors *)
(**
	The assertion [is_monP p v R Ψ1 Ψ2] means that [v] is a
	reference monitor (with progress bit [p]) of "type" [Ψ1 → Ψ2]
	where [Ψ1] and [Ψ2] are predicates on inputs of type [A] and
	outputs of type [B], respectively. Both [A] and [B] must have
	[constructor] instances.

	This is just a special case of [is_mon] where [Ψ2] does not
	depend on the input.
*)
Section is_monP.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.

  Definition is_monP (p : pbit) (v : val) (Ψ1 : A → iProp Σ)
      (Ψ2 : B → iProp Σ) : iProp Σ := is_mon p v Ψ1 (λ _, Ψ2).

  Lemma monP_triple p v Ψ1 Ψ2 :
    is_monP p v Ψ1 Ψ2 ⊣⊢
    (∀ a, {{{ Ψ1 a }}} v (fA a) @ p; ⊤ {{{ b, RET fB b; Ψ2 b }}})%I.
  Proof. by []. Qed.
End is_monP.
