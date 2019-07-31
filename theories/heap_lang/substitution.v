From iris.prelude Require Import countable decidable.
From iris.base_logic Require Import big_op.
From iris.heap_lang Require Export heap.
From iris.heap_lang Require addenda.
From iris.proofmode Require Import tactics.
Import addenda.list addenda.fin_maps.

Local Hint Resolve to_of_val.

(** * Substitution of values for binders *)
Section substitution.
  Context `{heapG Σ}.
  Implicit Types e : expr.
  Implicit Types v : val.

  Definition encode_binder (x : binder) : positive :=
    encode (if x is BNamed x then Some x else None).
  Definition decode_binder (p : positive) : option binder :=
    if decode p is Some opt then
      Some (if opt is Some x then BNamed x else BAnon)
    else None.
  Lemma decode_encode_binder x :
    decode_binder (encode_binder x) = Some x.
  Proof.
    case: x=>[|x]. by naive_solver.
    by rewrite/encode_binder/decode_binder decode_encode.
  Qed.
  Instance binder_countable : Countable binder := {|
    encode := encode_binder; decode := decode_binder;
    decode_encode := decode_encode_binder
  |}.

  Definition env := gmap binder val.
  Implicit Types γ : env.

  Definition substitute_acc : binder * val → (expr → expr) → expr → expr :=
    λ xv f, let: (x, v) := xv in λ e, subst' x (of_val v) (f e).
  Definition substitute' : list (binder * val) → expr → expr :=
    foldr substitute_acc id.
  Definition substitute : env → expr → expr := substitute' ∘ map_to_list.
  Coercion substitute : env >-> Funclass.

  Lemma substitute'_cons x v L e :
    substitute' ((x, v) :: L) e = subst' x (of_val v) (substitute' L e).
  Proof. by []. Qed.

  Notation ext R := (pointwise_relation _ R).
  Instance substitute_acc_proper :
    Proper ((=) ==> ext (=) ==> ext (=)) substitute_acc.
  Proof.
    move=>[x v] [??] [<-<-] f1 f2 EQf e. by rewrite/substitute_acc (EQf e).
  Qed.

  Lemma substitute'_proper L1 L2 :
    (∀ x v v', (x, v) ∈ L1 → (x, v') ∈ L1 → v = v') →
    L1 ≡ₚ L2 →
    ext (=) (substitute' L1) (substitute' L2).
  Proof.
    rewrite/substitute'=>Hfun EQ. elim: EQ Hfun=> {L1 L2}.
    - done.
    - move=>[x v] L1' L2' EQ IH Hfun.
      do 2!rewrite foldr_cons. apply substitute_acc_proper, IH.
      done. by intros; eapply Hfun, elem_of_cons; right.
    - move=>[x v] [y v'] L Hfun e.
      do 4!rewrite foldr_cons. rewrite {1 2 4 5}/substitute_acc.
      case: (decide (x = y))=>?; last by rewrite subst_subst_ne'.
      subst. do 2!rewrite subst_subst'. do 2!f_equal.
      eapply Hfun; last by apply elem_of_cons; left.
      apply elem_of_cons. right. apply elem_of_cons. by left.
    - move=>L1 L L2 EQ1 IH1 EQ2 IH2 Hfun.
      rewrite (IH1 Hfun) (IH2 _)=> // x v v' ??.
      by eapply Hfun; eapply elem_of_list_permutation_proper.
  Qed.

  Lemma subst_substitute γ x v e :
    γ !! x = None → subst' x (of_val v) (γ e) = (<[x:=v]>γ) e.
  Proof.
    move=>?. rewrite /substitute/compose -substitute'_cons.
    symmetry. apply substitute'_proper.
    exact: map_to_list_unique. by rewrite map_to_list_insert.
  Qed.

  Lemma substitute_closed γ e : Closed [] e → γ e = e.
  Proof.
    move=>?. induction γ as [|x v γ Hx IH] using map_ind; first done.
    rewrite -subst_substitute // IH.
    case: x Hx=> //= x Hx. exact: subst_is_closed_nil.
  Qed.

  Lemma substitute_empty e : (∅ : env) e = e. Proof. by []. Qed.

  Lemma substitute_expr γ e :
    γ e =
    match e with
    | Var x => default (Var x) (γ !! BNamed x) of_val
    | Rec f x e => Rec f x $ (delete f $ delete x $ γ) e
    | App e1 e2 => App (γ e1) (γ e2)
    | Lit _ | Unit | Loc _ => e
    | UnOp op e => UnOp op (γ e)
    | BinOp op e1 e2 => BinOp op (γ e1) (γ e2)
    | If e1 e2 e3 => If (γ e1) (γ e2) (γ e3)
    | Pair e1 e2 => Pair (γ e1) (γ e2)
    | Fst e => Fst (γ e)
    | Snd e => Snd (γ e)
    | InjL e => InjL (γ e)
    | InjR e => InjR (γ e)
    | Case e1 e2 e3 => Case (γ e1) (γ e2) (γ e3)
    | Assert e => Assert (γ e)
    | Fork e => Fork (γ e)
    | Alloc e => Alloc (γ e)
    | Load e => Load (γ e)
    | Store e1 e2 => Store (γ e1) (γ e2)
    | CAS e1 e2 e3 => CAS (γ e1) (γ e2) (γ e3)
    end.
  Proof.
    move: γ e.
    have nullary: ∀ γ e, (∀ x es, subst x es e = e) → γ e = e.
    { move=>γ e Hf.
      have{Hf} Hf: ∀ x es, subst' x es e = e by case.
      induction γ as [|x v γ Hx IH] using map_ind; first done.
      by rewrite -subst_substitute // IH Hf. }
    Local Ltac by_induction γ Hf :=
      let IH := fresh "IH" in
      induction γ as [|x v γ Hx IH] using map_ind; first done;
      by rewrite -subst_substitute // IH Hf; f_equal; rewrite subst_substitute.
    have unary: ∀ f γ e, (∀ x es e, subst x es (f e) = f (subst x es e)) →
      γ (f e) = f (γ e).
    { move=>f γ e Hf.
      have{Hf} Hf: ∀ x es e, subst' x es (f e) = f (subst' x es e) by case.
      by_induction γ Hf. }
    have binary: ∀ f γ e1 e2,
      (∀ x es e1 e2, subst x es (f e1 e2) = f (subst x es e1) (subst x es e2)) →
      substitute γ (f e1 e2) = f (substitute γ e1) (substitute γ e2).
    { move=>f γ e1 e2 Hf.
      have{Hf} Hf: ∀ x es e1 e2, subst' x es (f e1 e2) =
         f (subst' x es e1) (subst' x es e2) by case.
      by_induction γ Hf. }
    have ternary: ∀ f γ e1 e2 e3,
      (∀ x es e1 e2 e3, subst x es (f e1 e2 e3) =
       f (subst x es e1) (subst x es e2) (subst x es e3)) →
      γ (f e1 e2 e3) = f (γ e1) (γ e2) (γ e3).
    { move=>f γ e1 e2 e3 Hf.
      have{Hf} Hf: ∀ x es e1 e2 e3, subst' x es (f e1 e2 e3) =
        f (subst' x es e1) (subst' x es e2) (subst' x es e3) by case.
      by_induction γ Hf. }
    move=>γ /= []; try by auto using nullary, unary, binary, ternary.
    - move=> x {nullary unary binary ternary}.
      induction γ as [|y v γ Hy IH] using map_ind; first done.
      rewrite -subst_substitute // IH {IH}. case: (decide (BNamed x = y)) => ?.
      { subst. by rewrite Hy lookup_insert /= /subst decide_True. }
      rewrite lookup_insert_ne //. destruct y as [|y]; first done.
      case: (_ !! _)=>[?|] =>/=.
      + rewrite subst_is_closed_nil //. exact: is_closed_of_val.
      + rewrite/subst decide_False // => ?. by subst.
    - move=>f x e {nullary unary binary ternary}.
      induction γ as [|y v γ Hy IH] using map_ind; first done.
      rewrite -subst_substitute // IH {IH}.
      case: (decide (y ≠ f ∧ y ≠ x))=>[[??]| /not_and_l EQ].
      { rewrite subst_rec_ne'; [by left | by left|]. f_equal.
        rewrite subst_substitute; first by do 2!rewrite lookup_delete_ne //.
        by do 2!rewrite delete_insert_ne //. }
      rewrite subst_rec'; first by case: EQ=>/dec_stable; [left| right; left].
      do 2!f_equal. case: EQ=>/dec_stable ?; subst.
      + by rewrite delete_commute [delete f _]delete_notin //
          delete_commute delete_insert //.
      + f_equal. by rewrite delete_notin // delete_insert //.
  Qed.
End substitution.
