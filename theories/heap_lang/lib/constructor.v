From iris.heap_lang Require Export lang.

(** * Value constructors *)
(**
	The point of these instances is to leave implicit the
	injections into values we need to specify, say, finite maps
	implemented in the heap language.
*)

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
