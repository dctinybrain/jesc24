From iris.program_logic Require Export weakestpre ownp.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics addenda.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import fin_maps.
Import addenda.ectx_language addenda.ectx_lifting addenda.ownp.
Import uPred.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (strong_atomic _) => solve_atomic.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

Section lifting.
Context `{ownPG heap_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types e : expr.
Implicit Types v : val.
Implicit Types efs : list expr.
Implicit Types h : heap.
Implicit Types σ : state.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {p E e} K Φ :
  WP e @ p; E {{ v, WP fill K (of_val v) @ p; E {{ Φ }} }} ⊢ WP fill K e @ p; E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {p E e} Ki Φ :
  WP e @ p; E {{ v, WP fill_item Ki (of_val v) @ p; E {{ Φ }} }} ⊢
     WP fill_item Ki e @ p; E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_stuck_var x E Φ : True ⊢ WP Var x @ E ?{{ Φ }}.
Proof.
  apply wp_lift_pure_head_stuck=>// -[|Ki ?] /= ????? ?.
  by subst; inversion 1. by destruct Ki.
Qed.

Lemma wp_stuck_rec_open E f x e Φ :
  ¬ is_closed (f :b: x :b: []) e → WP Rec f x e @ E ?{{ Φ }}%I.
Proof.
  move=>?.
  apply wp_lift_pure_head_stuck; first by rewrite/=/to_val; case_decide.
  move=>[|Ki ?] /= ????? ?. by subst; inversion 1. by destruct Ki.
Qed.

Definition is_rec e : Prop := ∃ f x erec, Rec f x erec = e.

Global Instance is_rec_dec e : Decision (is_rec e).
Proof.
  rewrite /is_rec. case: e; try by intros; right; naive_solver.
  move=>f x e. left. by exists f, x, e.
Qed.

Lemma wp_stuck_app_nrec E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → ¬ is_rec e1 →
  WP App e1 e2 @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_rec=>???.
  apply wp_lift_pure_head_stuck=>// -[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst. naive_solver. }
  case: Ki Hfill=>//= ? [] ??; subst; apply: stuck_by_val Hstep; naive_solver.
Qed.

Lemma wp_stuck_app_open E e1 f x erec e2 v2 Φ :
  e1 = Rec f x erec → to_val e2 = Some v2 → ¬ Closed (f :b: x :b: []) erec →
  WP App e1 e2 @ E ?{{ Φ }}%I.
Proof.
  intros. apply wp_lift_pure_head_stuck=>//-[|Ki K] /= e ???? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep. naive_solver. }
  case: Ki Hfill=>//=.
  - move=>e2' [] He1' He2'. subst.
    have He: e = Rec f x erec by case: K He1' => //= -[].
    rewrite He in Hstep. by inversion Hstep as [].
  - move=>? [] ??; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

(* PDS: Misnamed. *)
Lemma wp_rec p E f x erec e1 e2 Φ :
  e1 = Rec f x erec →
  is_Some (to_val e2) →
  Closed (f :b: x :b: []) erec →
  ▷ WP subst' x e2 (subst' f e1 erec) @ p; E {{ Φ }} ⊢ WP App e1 e2 @ p; E {{ Φ }}.
Proof.
  intros -> [v2 ?] ?. rewrite -(wp_lift_pure_det_head_step_no_fork (App _ _)
    (subst' x e2 (subst' f (Rec f x erec) erec))); eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_stuck_un_op op E e v Φ :
  to_val e = Some v → un_op_eval op v = None →
  WP UnOp op e @ E ?{{ Φ }}%I.
Proof.
  intros. apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst. naive_solver. }
  case: Ki Hfill => //= ? [] ??; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_un_op p E op e v v' Φ :
  to_val e = Some v →
  un_op_eval op v = Some v' →
  ▷ Φ v' ⊢ WP UnOp op e @ p; E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step_no_fork (UnOp op _) (of_val v'))
    -?wp_value'; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_stuck_bin_op E op e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  bin_op_eval op v1 v2 = None →
  WP BinOp op e1 e2 @ E ?{{ Φ }}%I.
Proof.
  intros. apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep. naive_solver. }
  case: Ki Hfill => //= ?? [] ???; subst; apply: stuck_by_val Hstep; naive_solver.
Qed.

Lemma wp_bin_op p E op e1 e2 v1 v2 v' Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  bin_op_eval op v1 v2 = Some v' →
  ▷ (Φ v') ⊢ WP BinOp op e1 e2 @ p; E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step_no_fork (BinOp op _ _) (of_val v'))
    -?wp_value'; eauto.
  intros; inv_head_step; eauto.
Qed.

Definition is_lit_bool e : Prop := ∃ b, Lit (LitBool b) = e.

Global Instance is_lit_bool_dec e : Decision (is_lit_bool e).
Proof.
  rewrite /is_lit_bool. case: e; try by intros; right; naive_solver.
  case; try by intros; right; naive_solver. move=>b. left. by exists b.
Qed.

Lemma wp_stuck_if E e v e1 e2 Φ :
  to_val e = Some v → ¬ is_lit_bool e → WP If e e1 e2 @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_lit_bool=>??.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst; naive_solver. }
  case: Ki Hfill => //= ?? [] ???; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_if_true p E e1 e2 Φ :
  ▷ WP e1 @ p; E {{ Φ }} ⊢ WP If (Lit (LitBool true)) e1 e2 @ p; E {{ Φ }}.
Proof.
  apply wp_lift_pure_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_if_false p E e1 e2 Φ :
  ▷ WP e2 @ p; E {{ Φ }} ⊢ WP If (Lit (LitBool false)) e1 e2 @ p; E {{ Φ }}.
Proof.
  apply wp_lift_pure_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Definition is_pair_val e : Prop :=
  ∃ e1 e2, is_Some (to_val e1) ∧ is_Some (to_val e2) ∧ e = Pair e1 e2.

Global Instance is_pair_val_dec v : Decision (is_pair_val (of_val v)).
Proof.
  rewrite /is_pair_val. case: v; try by intros; right; naive_solver.
  move=>v1 v2. left. do 2!eexists. by eauto using to_of_val.
Qed.

Lemma wp_stuck_fst E e v Φ :
  to_val e = Some v → ¬ is_pair_val e → WP Fst e @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_pair_val=>? Hp.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ?? e2 ?? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst.
    apply: Hp. eexists e2, _. naive_solver. }
  case: Ki Hfill => //= [] ?; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_fst p E e1 v1 e2 Φ :
  to_val e1 = Some v1 → is_Some (to_val e2) →
  ▷ Φ v1 ⊢ WP Fst (Pair e1 e2) @ p; E {{ Φ }}.
Proof.
  intros ? [v2 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Fst _) e1) -?wp_value; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_stuck_snd E e v Φ :
  to_val e = Some v → ¬ is_pair_val e → WP Snd e @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_pair_val=>? Hp.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ?? e2 ?? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst.
    apply: Hp. exists e1, e2. naive_solver. }
  case: Ki Hfill => //= [] ?; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_snd p E e1 e2 v2 Φ :
  is_Some (to_val e1) → to_val e2 = Some v2 →
  ▷ Φ v2 ⊢ WP Snd (Pair e1 e2) @ p; E {{ Φ }}.
Proof.
  intros [v1 ?] ?.
  rewrite -(wp_lift_pure_det_head_step_no_fork (Snd _) e2) -?wp_value; eauto.
  intros; inv_head_step; eauto.
Qed.

Definition is_inj_val e : Prop :=
  ∃ e', is_Some (to_val e') ∧ (e = InjL e' ∨ e = InjR e').

Global Instance is_inj_val_dec v : Decision (is_inj_val (of_val v)).
Proof.
  rewrite /is_inj_val. destruct v; solve
    [by right; naive_solver | by left; eexists; eauto using to_of_val].
Qed.

Lemma wp_stuck_case E e v e1 e2 Φ :
  to_val e = Some v → ¬ is_inj_val e → WP Case e e1 e2 @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_inj_val=>? Hs.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst;
    apply: Hs; exists e0; naive_solver. }
  case: Ki Hfill => //= ?? [] ???; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_case_inl p E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e1 e0 @ p; E {{ Φ }} ⊢ WP Case (InjL e0) e1 e2 @ p; E {{ Φ }}.
Proof.
  intros [v0 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Case _ _ _) (App e1 e0)); eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_case_inr p E e0 e1 e2 Φ :
  is_Some (to_val e0) →
  ▷ WP App e2 e0 @ p; E {{ Φ }} ⊢ WP Case (InjR e0) e1 e2 @ p; E {{ Φ }}.
Proof.
  intros [v0 ?].
  rewrite -(wp_lift_pure_det_head_step_no_fork (Case _ _ _) (App e2 e0)); eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_assert p E e Φ :
  WP e @ p; E {{ v, ⌜v = LitV (LitBool true)⌝ ∧ ▷ Φ (LitV LitUnit) }} -∗
  WP Assert e @ p; E {{ Φ }}.
Proof.
  change (Assert e) with (fill [AssertCtx] e). rewrite -wp_bind.
  iIntros "He"; iApply (wp_wand with "[$He] []").
  iIntros (v) "[% ?]". subst. simpl.
  rewrite -(wp_lift_pure_det_head_step_no_fork (Assert _)) -?wp_value;
    eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_fork p E e Φ :
  ▷ Φ (LitV LitUnit) ∗ ▷ WP e @ p; ⊤ {{ _, True }} ⊢ WP Fork e @ p; E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) [e]) //=; eauto.
  - by rewrite later_sep -(wp_value _ _ _ (Lit _)) // big_sepL_singleton.
  - intros; inv_head_step; eauto.
Qed.

(** Base axioms for stateful reduction. *)
Lemma wp_alloc_pst p E σ h v :
  heap_of σ = h →
  {{{ ▷ ownP σ }}} Alloc (of_val v) @ p; E
  {{{ l, RET LitV (LitLoc l); ⌜h !! l = None⌝ ∧ ownP (hupd σ (<[l:=v]>h)) }}}.
Proof.
  iIntros (? Φ) "HP HΦ".
  iApply (ownP_lift_atomic_head_step (Alloc (of_val v)) σ); eauto.
  iFrame "HP". iNext. iIntros (e2 σ2 ef) "% HP". inv_head_step.
  iSplitL; last by iApply big_sepL_nil. iApply "HΦ". by iSplit.
Qed.

Definition is_loc e : Prop := ∃ l, e = Lit (LitLoc l).

Global Instance is_loc_dec e : Decision (is_loc e).
Proof.
  rewrite /is_loc. case: e; try by intros; right; naive_solver.
  case; try by intros; right; naive_solver. move=>l. left. by exists l.
Qed.

Lemma wp_stuck_load E e v Φ :
  to_val e = Some v → ¬ is_loc e → WP Load e @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_loc=>??.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst. naive_solver. }
  case: Ki Hfill=> //= [] ?; subst. apply: stuck_by_val Hstep. naive_solver.
Qed.

Lemma wp_load_pst p E σ h l v :
  heap_of σ = h → h !! l = Some v →
  {{{ ▷ ownP σ }}} Load (Lit (LitLoc l)) @ p; E {{{ RET v; ownP σ }}}.
Proof.
  intros ?? Φ. apply ownP_lift_atomic_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_stuck_store E e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 → ¬ is_loc e1 →
  WP Store e1 e2 @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_loc=>???.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst. naive_solver. }
  case: Ki Hfill=> //= ? [] ??; subst; apply: stuck_by_val Hstep; naive_solver.
Qed.

Lemma wp_store_pst p E σ h l v v' :
  heap_of σ = h → h !! l = Some v' →
  {{{ ▷ ownP σ }}} Store (Lit (LitLoc l)) (of_val v) @ p; E
  {{{ RET LitV LitUnit; ownP (hupd σ (<[l:=v]>h)) }}}.
Proof.
  intros. apply ownP_lift_atomic_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_stuck_cas E e0 v0 e1 v1 e2 v2 Φ :
  to_val e0 = Some v0 → to_val e1 = Some v1 → to_val e2 = Some v2 →
  ¬ is_loc e0 → WP CAS e0 e1 e2 @ E ?{{ Φ }}%I.
Proof.
  rewrite/is_loc=>????.
  apply wp_lift_pure_head_stuck=>//-[|Ki ?] /= ????? Hfill Hstep.
  { rewrite -Hfill in Hstep. inversion Hstep; subst; naive_solver. }
  case: Ki Hfill=> //= ?? [] ???; subst; apply: stuck_by_val Hstep; naive_solver.
Qed.

Lemma wp_cas_fail_pst p E σ h l v1 v2 v' :
  heap_of σ = h → h !! l = Some v' → v' ≠ v1 →
  {{{ ▷ ownP σ }}} CAS (Lit (LitLoc l)) (of_val v1) (of_val v2) @ p; E
  {{{ RET LitV $ LitBool false; ownP σ }}}.
Proof.
  intros. apply ownP_lift_atomic_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_cas_suc_pst p E σ h l v1 v2 :
  heap_of σ = h → h !! l = Some v1 →
  {{{ ▷ ownP σ }}} CAS (Lit (LitLoc l)) (of_val v1) (of_val v2) @ p; E
  {{{ RET LitV $ LitBool true; ownP (hupd σ (<[l:=v2]>h)) }}}.
Proof.
  intros. apply ownP_lift_atomic_det_head_step_no_fork; eauto.
  intros; inv_head_step; eauto.
Qed.

(** Proof rules for derived constructs *)
Lemma wp_lam p E x elam e1 e2 Φ :
  e1 = Lam x elam →
  is_Some (to_val e2) →
  Closed (x :b: []) elam →
  ▷ WP subst' x e2 elam @ p; E {{ Φ }} ⊢ WP App e1 e2 @ p; E {{ Φ }}.
Proof. intros. by rewrite -(wp_rec _ _ BAnon) //. Qed.

Lemma wp_let p E x e1 e2 Φ :
  is_Some (to_val e1) → Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ p; E {{ Φ }} ⊢ WP Let x e1 e2 @ p; E {{ Φ }}.
Proof. by apply wp_lam. Qed.

Lemma wp_seq p E e1 e2 Φ :
  is_Some (to_val e1) → Closed [] e2 →
  ▷ WP e2 @ p; E {{ Φ }} ⊢ WP Seq e1 e2 @ p; E {{ Φ }}.
Proof. intros ??. by rewrite -wp_let. Qed.

Lemma wp_skip p E Φ : ▷ Φ (LitV LitUnit) ⊢ WP Skip @ p; E {{ Φ }}.
Proof. rewrite -wp_seq; last eauto. by rewrite -wp_value. Qed.

Lemma wp_match_inl p E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x1 :b: []) e1 →
  ▷ WP subst' x1 e0 e1 @ p; E {{ Φ }} ⊢ WP Match (InjL e0) x1 e1 x2 e2 @ p; E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inl // -[X in _ ⊢ X]later_intro -wp_let. Qed.

Lemma wp_match_inr p E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x2 :b: []) e2 →
  ▷ WP subst' x2 e0 e2 @ p; E {{ Φ }} ⊢ WP Match (InjR e0) x1 e1 x2 e2 @ p; E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inr // -[X in _ ⊢ X]later_intro -wp_let. Qed.

Lemma wp_le p E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊢ ▷ Φ (LitV (LitBool true))) →
  (n2 < n1 → P ⊢ ▷ Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ p; E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt p E (n1 n2 : Z) P Φ :
  (n1 < n2 → P ⊢ ▷ Φ (LitV (LitBool true))) →
  (n2 ≤ n1 → P ⊢ ▷ Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp LtOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ p; E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq p E e1 e2 v1 v2 P Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  (v1 = v2 → P ⊢ ▷ Φ (LitV (LitBool true))) →
  (v1 ≠ v2 → P ⊢ ▷ Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp EqOp e1 e2 @ p; E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (v1 = v2)); by eauto.
Qed.
End lifting.
