From iris.heap_lang Require Export heap.
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

(** * Value constructors *)

Class constructor (A : Type) := Ctor {
  ctor : A → val;
  ctor_inj : Inj (=) (=) ctor
}.

Existing Instance ctor_inj.
Arguments Ctor {_} _ _.

Instance val_ctor : constructor val := Ctor id id_inj.

Lemma locv_inj : Inj (=) (=) LocV. Proof. by move=>?? [] ->. Qed.
Instance loc_constructor : constructor loc := Ctor LocV locv_inj.

Coercion ctor : constructor >-> Funclass.

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

(** * Reference monitors *)
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
      (Ψ2 : B → iProp Σ) : iProp Σ :=
    (∀ a, {{{ Ψ1 a }}} v (fA a) ?{{{ b, RET fB b; Ψ2 b }}})%I.

  Global Instance is_monP_persistent v Ψ1 Ψ2 :
    PersistentP (is_monP v Ψ1 Ψ2).
  Proof. apply _. Qed.

  Global Instance is_monP_ne v n :
     Proper (ext (dist n) ==> ext (dist n) ==> dist n) (is_monP v).
  Proof. solve_proper. Qed.

  Global Instance is_monP_proper v :
     Proper (ext (≡) ==> ext (≡) ==> (≡)) (is_monP v).
  Proof. solve_proper. Qed.

  Lemma is_monP_rel v Ψ1 Ψ2 :
    is_monP v Ψ1 Ψ2 ⊣⊢ is_mon v Ψ1 (λ _, Ψ2).
  Proof. by []. Qed.
End is_monP.
Typeclasses Opaque is_monP.
