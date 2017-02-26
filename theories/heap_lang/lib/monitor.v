From iris.heap_lang Require Export heap.
From iris.heap_lang.lib Require Export constructor.
From iris.heap_lang Require notation.

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
	The assertion [is_mon v Ψ1 Ψ2] means that [v] is a reference
	monitor of "type" [Ψ1 → Ψ2] where [Ψ1] is a predicate on
	inputs of type [A] and [Ψ2] relates inputs of type [A] to
	outputs of type [B]. Both [A] and [B] must have [constructor]
	instances.
*)
Section is_mon.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.

  Definition is_mon (v : val) (Ψ1 : A → iProp Σ)
      (Ψ2 : A → B → iProp Σ) : iProp Σ :=
    (∀ a, {{{ Ψ1 a }}} v (fA a) ?{{{ b, RET fB b; Ψ2 a b }}})%I.

  Global Instance is_mon_persistent v Ψ1 Ψ2 :
    PersistentP (is_mon v Ψ1 Ψ2).
  Proof. apply _. Qed.

  Global Instance is_mon_ne v n :
    Proper (ext (dist n) ==> ((=) ==> ext (dist n)) ==> dist n) (is_mon v).
  Proof. solve_proper_eq. Qed.

  Global Instance is_mon_proper v :
     Proper (ext (≡) ==> ((=) ==> ext (≡)) ==> (≡)) (is_mon v).
  Proof. solve_proper_eq. Qed.
End is_mon.
Typeclasses Opaque is_mon.

(** * Predicate-based reference monitors *)
(**
	The assertion [is_monP v Ψ1 Ψ2] means that [v] is a reference
	monitor of "type" [Ψ1 → Ψ2] where [Ψ1] and [Ψ2] are predicates
	on inputs of type [A] and outputs of type [B], respectively.
	Both [A] and [B] must have [constructor] instances.

	This is just a special case of [is_mon] where [Ψ2] does not
	depend on the input.
*)
Section is_monP.
  Context `{heapG Σ, fA : constructor A, fB : constructor B}.

  Definition is_monP (v : val) (Ψ1 : A → iProp Σ)
      (Ψ2 : B → iProp Σ) : iProp Σ := is_mon v Ψ1 (λ _, Ψ2).

  Lemma monP_triple v Ψ1 Ψ2 :
    is_monP v Ψ1 Ψ2 ⊣⊢ (∀ a, {{{ Ψ1 a }}} v (fA a) ?{{{ b, RET fB b; Ψ2 b }}})%I.
  Proof. by []. Qed.
End is_monP.
