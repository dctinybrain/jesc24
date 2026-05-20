From iris.base_logic Require Import big_op.
From iris.heap_lang Require addenda.
From iris.heap_lang Require Export heap on_val substitution.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Import tactics.
Import addenda.list addenda.fin_maps.
Import uPred.

Local Hint Resolve to_of_val.

(** * Contexts *)
(**
	The syntax of contexts is entirely standard, extending the
	syntax of expressions with a constructor [CHole] for holes.
*)
Inductive ctx :=
| CHole
| CVar (x : string)
| CRec (f : binder) (x : binder) (c : ctx)
| CApp (c1 c2 : ctx)
| CLit (lit : base_lit)
| CUnOp (op : un_op) (c : ctx)
| CBinOp (op : bin_op) (c1 c2 : ctx)
| CIf (c0 c1 c2 : ctx)
| CUnit
| CPair (c1 c2 : ctx)
| CFst (c : ctx)
| CSnd (c : ctx)
| CInjL (c : ctx)
| CInjR (c : ctx)
| CCase (c0 c1 c2 : ctx)
| CAssert (c : ctx)
| CFork (c : ctx)
| CLoc (l : loc)
| CAlloc (c : ctx)
| CLoad (c : ctx)
| CStore (c1 c2 : ctx)
| CCAS (c0 c1 c2 : ctx).

(** Embedding expressions [expr] in contexts [ctx]. *)
Definition ctx_to_expr : ctx → option expr :=
  fix go c :=
  match c with
  | CHole => None
  | CVar x => Some (Var x)
  | CRec f x c => e ← go c; Some (Rec f x e)
  | CApp c1 c2 => e1 ← go c1; e2 ← go c2; Some (App e1 e2)
  | CLit lit => Some (Lit lit)
  | CUnOp op c => e ← go c; Some (UnOp op e)
  | CBinOp op c1 c2 => e1 ← go c1; e2 ← go c2; Some (BinOp op e1 e2)
  | CIf c0 c1 c2 => e0 ← go c0; e1 ← go c1; e2 ← go c2; Some (If e0 e1 e2)
  | CUnit => Some Unit
  | CPair c1 c2 => e1 ← go c1; e2 ← go c2; Some (Pair e1 e2)
  | CFst c => e ← go c; Some (Fst e)
  | CSnd c => e ← go c; Some (Snd e)
  | CInjL c => e ← go c; Some (InjL e)
  | CInjR c => e ← go c; Some (InjR e)
  | CCase c0 c1 c2 => e0 ← go c0; e1 ← go c1; e2 ← go c2; Some (Case e0 e1 e2)
  | CAssert c => e ← go c; Some (Assert e)
  | CFork c => e ← go c; Some (Fork e)
  | CLoc l => Some (Loc l)
  | CAlloc c => e ← go c; Some (Alloc e)
  | CLoad c => e ← go c; Some (Load e)
  | CStore c1 c2 => e1 ← go c1; e2 ← go c2; Some (Store e1 e2)
  | CCAS c0 c1 c2 => e0 ← go c0; e1 ← go c1; e2 ← go c2; Some (CAS e0 e1 e2)
  end.
Definition ctx_of_expr : expr → ctx :=
  fix go e :=
  match e with
  | Var x => CVar x
  | Rec f x e => CRec f x (go e)
  | App e1 e2 => CApp (go e1) (go e2)
  | Lit lit => CLit lit
  | UnOp op e => CUnOp op (go e)
  | BinOp op e1 e2 => CBinOp op (go e1) (go e2)
  | If e0 e1 e2 => CIf (go e0) (go e1) (go e2)
  | Unit => CUnit
  | Pair e1 e2 => CPair (go e1) (go e2)
  | Fst e => CFst (go e)
  | Snd e => CSnd (go e)
  | InjL e => CInjL (go e)
  | InjR e => CInjR (go e)
  | Case e0 e1 e2 => CCase (go e0) (go e1) (go e2)
  | Assert e => CAssert (go e)
  | Fork e => CFork (go e)
  | Loc l => CLoc l
  | Alloc e => CAlloc (go e)
  | Load e => CLoad (go e)
  | Store e1 e2 => CStore (go e1) (go e2)
  | CAS e0 e1 e2 => CCAS (go e0) (go e1) (go e2)
  end.

Instance ctx_of_expr_inj : Inj (=) (=) ctx_of_expr.
Proof.
  intros e1. induction e1=>e2 ?; simplify_eq/=; destruct e2;
    simplify_eq/=; auto with f_equal.
Qed.
Lemma to_of_expr e : ctx_to_expr (ctx_of_expr e) = Some e.
Proof. by induction e; simplify_option_eq; repeat f_equal. Qed.
Lemma of_to_expr c e : ctx_to_expr c = Some e → ctx_of_expr e = c.
Proof.
  revert e. induction c; intros e ?; simplify_option_eq; auto with f_equal.
Qed.

(** * Multi-holed context plugging *)
(**
	Our multi-holed plugging operation plugs each hole, in turn,
	with the next expression from a list of plugees, using the
	dummy expression [Unit] when the list is exhausted and
	ignoring unneeded plugees.
*)
Definition plugM (A : Type) : Type := list expr → A * list expr.
Instance plugM_ret : MRet plugM := λ A x es, (x, es).
Instance plugM_bind : MBind plugM := λ A B f mx es,
  let p := mx es in f (p.1) (p.2).
Definition next_plugee : plugM expr := λ es,
  if es is e :: es then (e, es) else (Unit, []).	(* dummy *)
Definition ctx_plugM : ctx → plugM expr :=
  fix go c {struct c} :=
  let unary := λ f c, e ← go c; mret (f e) in
  let binary := λ f c1 c2, e1 ← go c1; unary (f e1) c2 in
  let ternary := λ f c0 c1 c2, e0 ← go c0; binary (f e0) c1 c2 in
  match c with
  | CHole => next_plugee
  | CVar x => mret (Var x)
  | CRec f x c => unary (Rec f x) c
  | CApp c1 c2 => binary App c1 c2
  | CLit lit => mret (Lit lit)
  | CUnOp op c => unary (UnOp op) c
  | CBinOp op c1 c2 => binary (BinOp op) c1 c2
  | CIf c0 c1 c2 => ternary If c0 c1 c2
  | CUnit => mret Unit
  | CPair c1 c2 => binary Pair c1 c2
  | CFst c => unary Fst c
  | CSnd c => unary Snd c
  | CInjL c => unary InjL c
  | CInjR c => unary InjR c
  | CCase c0 c1 c2 => ternary Case c0 c1 c2
  | CAssert c => unary Assert c
  | CFork c => unary Fork c
  | CLoc l => mret (Loc l)
  | CAlloc c => unary Alloc c
  | CLoad c => unary Load c
  | CStore c1 c2 => binary Store c1 c2
  | CCAS c0 c1 c2 => ternary CAS c0 c1 c2
  end.
Definition ctx_plug : ctx → list expr → expr := λ c es,
  (ctx_plugM c es).1.
Arguments ctx_plugM !_ _ / : assert.
Arguments ctx_plug !_ _ / : assert.

(** These tactics are probably overkill. *)
Local Tactic Notation "simpl_plug" :=
  repeat match goal with
  | H : context [mret (M:=plugM) ?x ?es] |- _ =>
    change (mret (M:=plugM) x es) with (x, es) in H
  | H : context [mbind (M:=plugM) ?f ?mx ?es] |- _ =>
    unfold mbind, plugM_bind in H
  | H1 : ctx_plugM ?c ?es = (_, _), H2 : context[ctx_plugM ?c ?es] |- _ =>
    rewrite H1 in H2
  | H : ctx_plugM ?c ?es = (_, _) |- context[ctx_plugM ?c ?es] =>
    idtac es; rewrite H
  end.
Local Tactic Notation "simplify_plug_eq" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | _ => progress simpl_plug
  end.
Local Tactic Notation "destruct_plug" "as" simple_intropattern(IP) :=
  match goal with
  | |- context[(ctx_plugM ?c ?es).1] =>
    destruct (ctx_plugM c es) as IP eqn:?; simplify_plug_eq
  end.

(** * Adversarial contexts *)
(**
	An _adversarial context_ contains no assertions and only low
	locations. (This is a syntactic criterion.)
*)
Section adv_ctx.
  Context `{heapG Σ}.

  Fixpoint adv_ctx (c : ctx) : iProp Σ :=
    match c with
    | CHole | CVar _ | CLit _ | CUnit => True
    | CAssert _ => False
    | CLoc l => low l
    | CRec _ _ c | CUnOp _ c | CFst c | CSnd c | CInjL c | CInjR c
    | CFork c | CAlloc c | CLoad c
      => adv_ctx c
    | CApp c1 c2 | CBinOp _ c1 c2 | CPair c1 c2 | CStore c1 c2
      => adv_ctx c1 ∗ adv_ctx c2
    | CIf c1 c2 c3 | CCase c1 c2 c3 | CCAS c1 c2 c3
      => adv_ctx c1 ∗ adv_ctx c2 ∗ adv_ctx c3
    end%I.
  Global Instance adv_ctx_timeless c : TimelessP (adv_ctx c).
  Proof. by elim: c=>//; apply _. Qed.
  Global Instance adv_ctx_persistent c : PersistentP (adv_ctx c).
  Proof. by elim: c=>//; apply _. Qed.
  Global Instance adv_ctx_ne : Proper ((=) ==> dist n) adv_ctx.
  Proof. apply _. Qed.
  Global Instance adv_ctx_proper : Proper ((=) ==> (≡)) adv_ctx.
  Proof. solve_proper. Qed.
End adv_ctx.
Typeclasses Opaque adv_ctx.

(** * Meta-level adversaries *)
(**
	To state the [robust_safety] theorem, we define a special case
	of adversarial contexts at the meta-level. A *(meta-level)
	adversary* is a context containing neither locations nor
	assertions.
*)
Fixpoint AdvCtx (c : ctx) : Prop :=
  match c with
  | CHole | CVar _ | CLit _ | CUnit => True
  | CAssert _ | CLoc _ => False
  | CRec _ _ c | CUnOp _ c | CFst c | CSnd c | CInjL c | CInjR c
  | CFork c | CAlloc c | CLoad c
    => AdvCtx c
  | CApp c1 c2 | CBinOp _ c1 c2 | CPair c1 c2 | CStore c1 c2
    => AdvCtx c1 ∧ AdvCtx c2
  | CIf c0 c1 c2 | CCase c0 c1 c2 | CCAS c0 c1 c2
    => AdvCtx c0 ∧ AdvCtx c1 ∧ AdvCtx c2
  end.

Lemma adv_ctx_intro `{heapG Σ} c : AdvCtx c → adv_ctx c.
Proof.
  rewrite/uPred_valid. elim: c=>//=; intros;
    repeat match goal with
    | H : AdvCtx _ ∧ _ |- _ => destruct H
    | IH : ?p → _, H : ?p |- _ => specialize (IH H); clear H
    | IH : True ⊢ adv_ctx ?c |- True ⊢ adv_ctx ?c ∗ _ =>
      rewrite -IH left_id; clear IH
    | H : ?p |- ?p => exact H
    end.
Qed.

(** * Robust safety *)
(**
	Our aim is to show that, under the heap invariant, if we plug
	a bunch of semantically low expressions (i.e., code verified
	to return a low value) into an adversarial context, the
	resulting expression is semantically low.

	The proof is by induction on contexts.
*)
Section robust_safety.
  Context `{heapG Σ}.
  Implicit Types γ : env.
  Implicit Types c : ctx.
  Implicit Types e : expr.
  Implicit Types v : val.

  (** Low environments send all binders to low values. *)
  Global Instance env_low : LowIntegrity Σ env :=
    Low (λ γ, [∗ map] v ∈ γ, low v)%I _ _.
  Lemma low_env γ : low γ ⊣⊢ [∗ map] v ∈ γ, low v. Proof. by []. Qed.

  Lemma low_env_empty : low (∅ : env) ⊣⊢ True.
  Proof. exact: big_sepM_empty. Qed.
  Lemma low_env_insert γ x v :
    γ !! x = None → low v -∗ low γ -∗ low (<[x:=v]>γ).
  Proof.
    do 2!rewrite low_env. move=>?. rewrite big_sepM_insert //.
    iIntros. by iFrame "#".
  Qed.
  Lemma low_env_singleton x v : low ({[x:=v]} : env) ⊣⊢ low v.
  Proof. exact: big_sepM_singleton. Qed.
  Lemma low_env_lookup γ x v : γ !! x = Some v → low γ -∗ low v.
  Proof. exact: big_sepM_lookup. Qed.
  Lemma low_env_delete γ x  : low γ -∗ low (delete x γ).
  Proof.
    rewrite low_env. apply big_sepM_mono. exact: delete_subseteq. done.
  Qed.

  (**
	An expression is *semantically low* if it is verified (under
	the heap invariant) to either get stuck or return a low value.

	To deal with binders inductively, we generalize using a
	substitution [γ] sending binders to low values. In contrast to
	most work on logical relations, [γ] need not be a closing
	substitution (because we permit a low expression to get
	stuck).

	The always modality makes [low_expr] persistent, which we need
	in the proof that function contexts [CRec f x c] are
	compatibile.
  *)
  Definition low_expr : expr → iProp Σ := λ e, (
    □ ∀ γ, heap_ctx -∗ low γ -∗ WP γ e ?{{ low }}
  )%I.

  (**
	As an important special case of low expressions, we say that
	an expression is *verified code* if it is closed and verified
	(under the heap invariant) to always returns a low value.

	This is the notion of verified code used in the
	[robust_safety] theorem.
  *)
  Definition verified_code : expr → iProp Σ := λ e, (
    □ ∃ p, ⌜Closed [] e⌝ ∗ (heap_ctx -∗ WP e @ p; ⊤ {{ low }})
  )%I.
  (** Verified code satisfies [low_expr] (because it is closed). *)
  Lemma verified_low e : verified_code e -∗ low_expr e.
  Proof.
    iDestruct 1 as (p) "#[% He]".
    iIntros "!#". iIntros (γ) "Hh _". rewrite substitute_closed.
    rewrite -(wp_forget_progress p). iApply ("He" with "Hh").
  Qed.

  (**
	A context is *semantically low* if, when plugged with low
	expressions, it produces a low expression.
  *)
  Definition low_ctx : ctx → iProp Σ := λ c, (
    ∀ es, ([∗ list] e ∈ es, low_expr e) -∗ low_expr (ctx_plug c es)
  )%I.

  (**
	A context is *compatible* (with the logical relation
	underlying low values) if, when it is adversarial, it is also
	low. Compatibility lifts the syntactic [adv_ctx] to the
	semantic [low_ctx].
  *)
  Definition compatible_ctx : ctx → iProp Σ := λ c, (
    adv_ctx c -∗ low_ctx c
  )%I.

  (**
	For our induction on contexts to go through, we strengthen
	[low_ctx] and [compatible_ctx] to speak in terms of the
	[ctx_plugM] operation and its state [es : list expr].
  *)
  Definition low_ctxM : ctx → iProp Σ := λ c, (
    ∀ es e' es', ⌜ctx_plugM c es = (e', es')⌝ -∗
    ([∗ list] e ∈ es, low_expr e) -∗
    low_expr e' ∗ ([∗ list] e ∈ es', low_expr e)
  )%I.
  Definition compatible_ctxM : ctx → iProp Σ := λ c, (
    adv_ctx c -∗ low_ctxM c
  )%I.
  Lemma compatible_ctx_intro c : compatible_ctxM c -∗ compatible_ctx c.
  Proof.
    iIntros "Hc Hadv". iIntros (es) "Hes".
    iSpecialize ("Hc" with "Hadv"). rewrite/ctx_plug. destruct_plug as [e' es'].
    iSpecialize ("Hc" $! es e' es' with "[%] Hes"); first done.
    by iDestruct "Hc" as "[$ _]".
  Qed.

  (**
	We use the following characterization of [compatible_ctxM] as
	it's easier to work under the Iris proof mode.
  *)
  Definition compatible : ctx → iProp Σ := λ c, (
    ∀ es e' es', ⌜ctx_plugM c es = (e', es')⌝ -∗ adv_ctx c -∗
    ([∗ list] e ∈ es, low_expr e) -∗
    low_expr e' ∗ ([∗ list] e ∈ es', low_expr e)
  )%I.
  Lemma compatible_spec c : compatible c ⊣⊢ compatible_ctxM c.
  Proof.
    apply equiv_spec; split.
    - iIntros "Hc Hadv". iIntros (es e' es' ?) "Hes".
      by iApply ("Hc" $! es e' es' with "[%] Hadv Hes").
    - iIntros "Hc". iIntros (es e' es' ?) "Hadv Hes".
      iSpecialize ("Hc" with "Hadv").
      by iApply ("Hc" $! es e' es' with "[%] Hes").
  Qed.

  (**
	For non-hole contexts, we need some boilerplate reasoning
	about the context plugging operation to reduce compatibility
	for contexts to a relation between low expressions.

	The following three lemmas implement that boilerplate. (Coq
	solves the complicated-looking side-conditions automatically.)
  *)
  Lemma compatible_nullary e c :
    ctx_plugM c = mret e → low_expr e → compatible c.
  Proof.
    iIntros (Hnullary Hlow). iIntros (es e' es' Hplug) "_ Hes".
    rewrite Hnullary{Hnullary} in Hplug. simplify_plug_eq. iFrame "Hes".
    by rewrite -Hlow.
  Qed.

  Lemma compatible_unary (f : expr → expr) (g : ctx → ctx) c :
    ctx_plugM (g c) = e ← ctx_plugM c; mret (f e) →
    (adv_ctx (g c) -∗ adv_ctx c) →
    (∀ e, low_expr e -∗ low_expr (f e)) →
    compatible c -∗ compatible (g c).
  Proof.
    iIntros (Hunary Hadv Hlow) "IHc". iIntros (es e' es' Hplug) "Hadv Hes".
    rewrite Hadv{Hadv}. rewrite Hunary{Hunary} in Hplug. simplify_plug_eq.
    destruct_plug as [e es1].
    iDestruct ("IHc" $! _ _ _ with "[%] Hadv Hes") as "[He $]"; first done.
    iApply (Hlow with "He").
  Qed.

  Lemma compatible_binary (f : expr → expr → expr) (g : ctx → ctx → ctx) c1 c2 :
    ctx_plugM (g c1 c2) = e1 ← ctx_plugM c1; e2 ← ctx_plugM c2; mret (f e1 e2) →
    (adv_ctx (g c1 c2) -∗ adv_ctx c1 ∗ adv_ctx c2) →
    (∀ e1 e2, low_expr e1 -∗ low_expr e2 -∗ low_expr (f e1 e2)) →
    compatible c1 ∗ compatible c2 -∗ compatible (g c1 c2).
  Proof.
    iIntros (Hbinary Hadv Hlow) "[IHc1 IHc2]". iIntros (es e' es' Hplug).
    rewrite Hadv{Hadv}. iIntros "[Hadv1 Hadv2] Hes".
    rewrite Hbinary{Hbinary} in Hplug. simplify_plug_eq.
    destruct_plug as [e1 es1].
    iDestruct ("IHc1" $! _ _ _ with "[%] Hadv1 Hes") as "[He1 Hes]"; first done.
    destruct_plug as [e2 es2].
    iDestruct ("IHc2" $! _ _ _ with "[%] Hadv2 Hes") as "[He2 $]"; first done.
    iApply (Hlow with "He1 He2").
  Qed.

  Lemma compatible_ternary (f : expr → expr → expr → expr)
      (g : ctx → ctx → ctx → ctx) c0 c1 c2 :
    ctx_plugM (g c0 c1 c2) =
      e0 ← ctx_plugM c0; e1 ← ctx_plugM c1; e2 ← ctx_plugM c2;
      mret (f e0 e1 e2) →
    (adv_ctx (g c0 c1 c2) -∗ adv_ctx c0 ∗ adv_ctx c1 ∗ adv_ctx c2) →
    (∀ e0 e1 e2, low_expr e0 -∗ low_expr e1 -∗ low_expr e2 -∗
     low_expr (f e0 e1 e2)) →
    compatible c0 ∗ compatible c1 ∗ compatible c2 -∗
    compatible (g c0 c1 c2).
  Proof.
    iIntros (Hternary Hadv Hlow) "(IHc0&IHc1&IHc2)". iIntros (es e' es' Hplug).
    rewrite Hadv{Hadv}. iIntros "(Hadv0&Hadv1&Hadv2) Hes".
    rewrite Hternary{Hternary} in Hplug. simplify_plug_eq.
    destruct_plug as [e0 es0].
    iDestruct ("IHc0" $! _ _ _ with "[%] Hadv0 Hes") as "[He0 Hes]"; first done.
    destruct_plug as [e1 es1].
    iDestruct ("IHc1" $! _ _ _ with "[%] Hadv1 Hes") as "[He1 Hes]"; first done.
    destruct_plug as [e2 es2].
    iDestruct ("IHc2" $! _ _ _ with "[%] Hadv2 Hes") as "[He2 $]"; first done.
    iApply (Hlow with "He0 He1 He2").
  Qed.

  (**
	[Unit] is special because we need the fact that it's
	semantically low twice. Once when showing [CHole] compatible
	(because unit is the dummy expression used when there are no
	plugees), and once when showing that [CUnit] is compatible.
  *)
  Lemma low_expr_Unit : True ⊢ low_expr Unit.
  Proof.
    iIntros "!#". iIntros (γ) "_ _". rewrite substitute_expr.
    iApply wp_value; first done. by rewrite low_val.
  Qed.

  Lemma compatible_CHole : True ⊢ compatible CHole.
  Proof.
    iIntros (es e' es' ?) "_ Hes". destruct es as [|e es]; simplify_plug_eq.
    - iFrame "Hes". by rewrite -low_expr_Unit.
    - by rewrite big_sepL_cons.
  Qed.
  Hint Extern 1 (_ ⊢ compatible CHole) => rewrite -compatible_CHole.

  Lemma compatible_CVar x : True ⊢ compatible (CVar x).
  Proof.
    rewrite compatible_nullary=>//.
    iIntros "!#". iIntros (γ) "_ Hγ". rewrite substitute_expr.
    case Hdom: (_ !! _)=>[v|]/=; last by iApply wp_stuck_var.
    iApply wp_value'. by iApply (low_env_lookup with "Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CVar _)) => rewrite -compatible_CVar.

  Lemma compatible_CRec f x c : compatible c -∗ compatible (CRec f x c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "#Hh #Hγ". rewrite substitute_expr.
    set erec := substitute _ _.
    case: (decide (Closed (f :b: x :b: []) erec)) => ?;
      last by iApply wp_stuck_rec_open.
    iApply wp_value; first exact: to_val_rec.
    rewrite/erec. set γ' := (delete _ _).
    iLöb as "Hvrec". rewrite {2}low_val. iAlways. iNext.
    iIntros (v2) "#Hv2". case: (decide (x = f))=>?.
    { subst. rewrite -> subst_subst'; last done.	(* ssr rewrite fails *)
      rewrite of_val_rec subst_substitute; first by rewrite lookup_delete.
      iApply ("IHe" with "Hh []").
      rewrite insert_delete. iApply (low_env_insert with "Hvrec");
        first by rewrite lookup_delete.
      by iApply (low_env_delete with "Hγ"). }
    rewrite of_val_rec subst_substitute; first by rewrite lookup_delete.
    rewrite subst_substitute; first by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply ("IHe" with "Hh []").
    iApply (low_env_insert with "Hv2"); first by rewrite
      lookup_insert_ne // lookup_delete_ne // lookup_delete.
    iApply (low_env_insert with "Hvrec"); first by rewrite
      lookup_delete.
    do 2!iApply low_env_delete. iExact "Hγ".
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CRec _ _ _)) => rewrite -compatible_CRec.

  Lemma compatible_CApp c1 c2 :
    compatible c1 ∗ compatible c2 -∗ compatible (CApp c1 c2).
  Proof.
    rewrite compatible_binary=>//{c1 c2}e1 e2.
    iIntros "#IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ". rewrite substitute_expr.
    iApply (wp_on_val_app_bind with "[]").
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CApp _ _)) => rewrite -compatible_CApp.

  Lemma compatible_CLit lit : True ⊢ compatible (CLit lit).
  Proof.
    rewrite compatible_nullary=>//.
    iIntros "!#". iIntros (γ) "_ _". rewrite substitute_expr.
    iApply wp_value; first done. by rewrite low_val.
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CLit _)) => rewrite -compatible_CLit.

  Lemma compatible_CUnOp op c : compatible c -∗ compatible (CUnOp op c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    iApply wp_on_val_un_op_bind. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CUnOp _ _)) => rewrite -compatible_CUnOp.

  Lemma compatible_CBinOp op c1 c2 :
    compatible c1 ∗ compatible c2 -∗ compatible (CBinOp op c1 c2).
  Proof.
    rewrite compatible_binary=>//{c1 c2}e1 e2.
    iIntros "#IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ". rewrite substitute_expr.
    iApply (wp_on_val_bin_op_bind with "[IHe1]").
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CBinOp _ _ _)) => rewrite -compatible_CBinOp.

  Lemma compatible_CIf c0 c1 c2 :
    compatible c0 ∗ compatible c1 ∗ compatible c2 -∗ compatible (CIf c0 c1 c2).
  Proof.
    rewrite compatible_ternary=>//{c0 c1 c2}e0 e1 e2.
    iIntros "#IHe0 #IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ".
    rewrite substitute_expr. wp_apply (wp_any_if_bind with "[]"); last iSplit.
    - by iApply ("IHe0" with "Hh Hγ").
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CIf _ _ _)) => rewrite -compatible_CIf.

  Lemma compatible_CUnit : True ⊢ compatible CUnit.
  Proof. rewrite compatible_nullary//. exact: low_expr_Unit. Qed.
  Hint Extern 1 (_ ⊢ compatible CUnit) => rewrite -compatible_CUnit.

  Lemma compatible_CPair c1 c2 :
    compatible c1 ∗ compatible c2 -∗ compatible (CPair c1 c2).
  Proof.
    rewrite compatible_binary=>//{c1 c2}e1 e2.
    iIntros "#IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ".
    rewrite substitute_expr. iApply (wp_on_val_pair_bind with "[]").
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CPair _ _)) => rewrite -compatible_CPair.

  Lemma compatible_CFst c : compatible c -∗ compatible (CFst c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    iApply wp_on_val_fst_bind. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CFst _)) => rewrite -compatible_CFst.

  Lemma compatible_CSnd c : compatible c -∗ compatible (CSnd c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    iApply wp_on_val_snd_bind. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CSnd _)) => rewrite -compatible_CSnd.

  Lemma compatible_CInjL c : compatible c -∗ compatible (CInjL c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    iApply wp_on_val_inl_bind. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CInjL _)) => rewrite -compatible_CInjL.

  Lemma compatible_CInjR c : compatible c -∗ compatible (CInjR c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    iApply wp_on_val_inr_bind. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CInjR _)) => rewrite -compatible_CInjR.

  Lemma compatible_CCase c0 c1 c2 :
    compatible c0 ∗ compatible c1 ∗ compatible c2 -∗
    compatible (CCase c0 c1 c2).
  Proof.
    rewrite compatible_ternary=>//{c0 c1 c2}e0 e1 e2.
    iIntros "#IHe0 #IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ".
    rewrite substitute_expr.
    wp_apply (wp_on_val_case_bind with "[]"); last (iIntros (v) "Hv"; iSplit).
    - by iApply ("IHe0" with "Hh Hγ").
    - iApply (wp_on_val_app_bind with "[-Hv]").
      by iApply ("IHe1" with "Hh Hγ"). by wp_value.
    - iApply (wp_on_val_app_bind with "[-Hv]").
      by iApply ("IHe2" with "Hh Hγ"). by wp_value.
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CCase _ _ _)) => rewrite -compatible_CCase.

  (**
	[CAssert] is special because it cannot occur in adversarial
	contexts.
  *)
  Lemma compatible_CAssert c : True ⊢ compatible (CAssert c).
  Proof. iIntros (es e' es' _) "/= Hadv". by iExFalso. Qed.
  Hint Extern 1 (_ ⊢ compatible (CAssert _)) => rewrite -compatible_CAssert.

  Lemma compatible_CFork c : compatible c -∗ compatible (CFork c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "Hh Hγ". rewrite substitute_expr.
    wp_apply wp_on_val_fork. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CFork _)) => rewrite -compatible_CFork.

  (**
	[CLoc] is special because all locations in adversarial
	contexts are low.
  *)
  Lemma compatible_CLoc l : True ⊢ compatible (CLoc l).
  Proof.
    iIntros (es e es' ?) "#Hadv Hes". simplify_plug_eq. iFrame "Hes".
    iIntros "!#". iIntros (γ) "_ _". rewrite substitute_expr.
    iApply wp_value; first done. by rewrite low_val.
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CLoc _)) => rewrite -compatible_CLoc.

  Lemma compatible_CAlloc c : compatible c -∗ compatible (CAlloc c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "#Hh Hγ". rewrite substitute_expr.
    iApply (wp_low_alloc_bind with "Hh"). done. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CAlloc _)) => rewrite -compatible_CAlloc.

  Lemma compatible_CLoad c : compatible c -∗ compatible (CLoad c).
  Proof.
    rewrite compatible_unary=>//{c}e.
    iIntros "#IHe !#". iIntros (γ) "#Hh Hγ". rewrite substitute_expr.
    iApply (wp_low_load_bind with "Hh"). done. by iApply ("IHe" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CLoad _)) => rewrite -compatible_CLoad.

  Lemma compatible_CStore c1 c2 :
    compatible c1 ∗ compatible c2 -∗ compatible (CStore c1 c2).
  Proof.
    rewrite compatible_binary=>//{c1 c2}e1 e2.
    iIntros "#IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ". rewrite substitute_expr.
    iApply (wp_low_store_bind with "Hh []"); first done.
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CStore _ _)) => rewrite -compatible_CStore.

  Lemma compatible_CCAS c0 c1 c2 :
    compatible c0 ∗ compatible c1 ∗ compatible c2 -∗
    compatible (CCAS c0 c1 c2).
  Proof.
    rewrite compatible_ternary=>//{c0 c1 c2}e0 e1 e2.
    iIntros "#IHe0 #IHe1 #IHe2 !#". iIntros (γ) "#Hh #Hγ". rewrite substitute_expr.
    iApply (wp_low_cas_bind with "Hh [] []"); first done.
    - by iApply ("IHe0" with "Hh Hγ").
    - by iApply ("IHe1" with "Hh Hγ").
    - by iApply ("IHe2" with "Hh Hγ").
  Qed.
  Hint Extern 1 (_ ⊢ compatible (CCAS _ _ _)) => rewrite -compatible_CCAS.

  Hint Extern 2 =>
    match goal with
    | IH : True ⊢ compatible ?c |- True ⊢ compatible (_ ?c) => rewrite IH
    end.
  Hint Extern 2 =>
    match goal with
    | IH1 : True ⊢ compatible ?c1, IH2 : True ⊢ compatible ?c2
      |- True ⊢ compatible (_ ?c1 ?c2)
      => rewrite (True_sep_1 True) {1}IH1 IH2
    end.
  Hint Extern 2 =>
    match goal with
    | IH1 : True ⊢ compatible ?c1, IH2 : True ⊢ compatible ?c2,
      IH3 : True ⊢ compatible ?c3 |- True ⊢ compatible (_ ?c1 ?c2 ?c3)
      => rewrite (True_sep_1 True) {2}(True_sep_1 True) {1}IH1 {1}IH2 IH3
    end.

  (**
	The fundamental theorem of robust safety: all adversarial
	contexts are semantically low.
  *)
  Theorem fundamental_theorem_robust_safety c : compatible_ctx c.
  Proof.
    rewrite/uPred_valid -compatible_ctx_intro -compatible_spec.
    by induction c; auto.
  Qed.

  (**
	The internal version of [robust_safety]: the expression
	obtained by plugging an adversarial context with verified code
	is, under the heap invariant, semantically low.
  *)
  Corollary robust_safetyI c es :
    heap_ctx ⊢ adv_ctx c -∗ ([∗ list] e ∈ es, verified_code e) -∗
    WP ctx_plug c es ?{{ low }}.
  Proof.
    iIntros "Hh Hadv Hes". setoid_rewrite verified_low.
    iPoseProof (fundamental_theorem_robust_safety with "Hadv") as "Hc".
    iSpecialize ("Hc" $! _ with "Hes").
    iSpecialize ("Hc" $! (∅ : env) with "Hh").
    by rewrite low_env_empty wand_True substitute_empty.
  Qed.
End robust_safety.

(** * Fundamental theorem of logical relations. *)
(**
	The fundamental theorem of logical relations is an easy corollary
	of the fundamental theorem of robust safety. We just need a few
	definitions to set it up and a few facts about contexts.

	(We don't actually need this theorem.)
*)

(**
	An expression is *adversarial* if it contains no assertions
	and only low locations. (This is a syntactic notion.)
*)
Section adv_expr.
  Context `{heapG Σ}.

  Definition adv_expr : expr → iProp Σ := adv_ctx ∘ ctx_of_expr.

  Lemma adv_expr_elim e :
    adv_expr e =
    match e with
    | Var _ | Lit _ | Unit => True
    | Assert _ => False
    | Loc l => low l
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e | InjR e
    | Fork e | Alloc e | Load e
      => adv_expr e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2
      => adv_expr e1 ∗ adv_expr e2
    | If e1 e2 e3 | Case e1 e2 e3 | CAS e1 e2 e3
      => adv_expr e1 ∗ adv_expr e2 ∗ adv_expr e3
    end%I.
  Proof. by induction e. Qed.
  Global Instance adv_expr_timeless e : TimelessP (adv_expr e).
  Proof. apply _. Qed.
  Global Instance adv_expr_persistent e : PersistentP (adv_expr e).
  Proof. apply _. Qed.
  Global Instance adv_expr_ne : Proper ((=) ==> dist n) adv_expr.
  Proof. apply _. Qed.
  Global Instance adv_expr_proper : Proper ((=) ==> (≡)) adv_expr.
  Proof. solve_proper. Qed.
End adv_expr.
Typeclasses Opaque adv_expr.
(*Arguments adv_expr {_ _} !_ / : assert.*)

Section ftlr.
  Context `{heapG Σ}.

  (**
	An expression is *compatible* (with the logical relation
	underlying low values) if, when it is adversarial, it is also
	semantically low. Compatibility lifts the syntactic [adv_expr]
	to the semantic [low_expr].
  *)
  Definition compatible_expr : expr → iProp Σ := λ e, (
    adv_expr e -∗ low_expr e
  )%I.

  Lemma ctx_plug_of e es : ctx_plug (ctx_of_expr e) es = e.
  Proof.
    move: e es.
    suff ctx_plugM_of e es : ctx_plugM (ctx_of_expr e) es = (e, es).
    { intros. by rewrite/ctx_plug ctx_plugM_of. }
    elim: e=>//=; intros;
    repeat match goal with
    | H : ctx_plugM ?e ?es = _ |- (ctx_plugM ?e ≫= _) ?es = _ =>
        rewrite/mbind/plugM_bind H /=; clear H
    | H : ctx_plugM ?e ?es = _ |- context [ctx_plugM ?e ?es] =>
        rewrite H; clear H
    end; reflexivity.
  Qed.
  Lemma adv_ctx_of e : adv_expr e -∗ adv_ctx (ctx_of_expr e).
  Proof. by []. Qed.

  Theorem fundamental_theorem_logical_relations e : compatible_expr e.
  Proof.
    iIntros "Hadv".
    iPoseProof (fundamental_theorem_robust_safety (ctx_of_expr e)) as "Hc".
    rewrite/compatible_ctx -adv_ctx_of. iSpecialize ("Hc" with "Hadv").
    iSpecialize ("Hc" $! []). by rewrite big_sepL_nil ctx_plug_of wand_True.
  Qed.
End ftlr.
