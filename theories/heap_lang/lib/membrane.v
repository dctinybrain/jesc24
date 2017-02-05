From iris.heap_lang Require Export heap.
From iris.heap_lang Require notation.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
Import uPred.

(** * Membrane code *)
(**
	The membrane constructs values that may be safely shared with
	adversarial code (i.e., values in [lowval ≡ on_val lowloc]).

	To read the code, it helps to have a spec in mind. Roughly,
	our specification says that if [locout : Ψ → lowloc] and
	[locin : lowloc → Ψ] for some "type" [Ψ] of locations, then
	[membrane locout locin : on_val Ψ → on_val lowloc]; that is,
	the membrane lifts reference monitors for locations to
	reference monitors for values. See [membrane_spec] and the
	special case [inert_membrane_spec].
*)
Section code.
  Import notation.
  Definition membrane : val := rec: "membrane" "locout" "locin" "x" :=
    let: "wrap" := "membrane" "locout" "locin" in
    iffun: "x" as "f" =>
      let: "unwrap" := "membrane" "locin" "locout" in
      λ: "y", "wrap" ("f" ("unwrap" "y"))
    else iflit: "x" as "lit" =>
      ifloc: "lit" as "l" => "locout" "l" else "lit"
    else ifpair: "x" as "p" =>
      let: "v1" := "wrap" (Fst "p") in
      let: "v2" := "wrap" (Snd "p") in
      ("v1", "v2")
    else ifinl: "x" as "x" => InjL ("wrap" "x")
    else ifinr: "x" as "x" => InjR ("wrap" "x")
    else assert: #false.
End code.

(**
	The membrane's main ingredient is its treatment of functions.
	(We made some inessential choices in writing this code. One
	need not preserve the structure of values or only apply
	reference monitors to locations.)

	The membrane does not offer unconditional safety. It avoids
	leaking high values to the adversary, but does not prevent the
	adversary from applying wrapped functions to "wrong" inputs,
	which is another way to interfere with otherwise safe code.
	The function [two ≔ λ r, assert (!r = 2)], for example, may be
	safely applied to any location containing the value 2 and to
	any non-location. In general, we may share neither [two] nor
	[wrap two] with the adversary. To see that [two] is unsafe,
	pick [C[•] := • (ref 1)]. To see that [wrap two] is unsafe,
	assume locations [ℓ], [ℓ'] such that [ℓ] is low and [locin ℓ]
	returns [ℓ'] and [ℓ'] contains the value 1. (This situation
	can easily arise when [locin] and [locout] maintain a partial
	bijection on locations and some verified code wraps [ℓ'].)
	Now, pick [C[•] := • ℓ].

	So, any membrane spec must make an assumption about the value
	to be wrapped. To verify the function case, any such
	assumption must imply WP for the bodies of wrapped functions.
	Can we use a simple syntactic restriction and, internally, a
	logical relation to obtain the necessary WP? Yes, but there is
	little point. If our restriction implies syntactic lowness,
	then the robust safety theorem says every restricted
	expression is semantically low, and the membrane buys us
	nothing. Now, our restriction *must* imply syntactic lowness.
	Our restriction must rule out assertions as the function [wrap
	(λ_. assert false)] is unsafe. Our restriction must rule out
	high locations (or heap operations, a non-starter). This is
	necessary because, to prove the FTLR, we must show that if [ℓ]
	is compatible, so is [! ℓ], and we're working under the heap
	invaraint.
*)

(** * Reference monitors *)
(**
	The assertion [is_mon v Ψ1 Ψ2] means that [v] is a reference
	monitor of "type" [Ψ1 → Ψ2] where the [Ψ_i] are predicates on
	some type [A] that may be injected into values. (We care about
	[A = loc] and [A = val].)
*)
Section is_mon.
  Context `{heapG Σ} {A : Type} (f : A → val).
  Notation ext R := (pointwise_relation _ R).

  Definition is_mon (v : val) (Ψ1 Ψ2 : A → iProp Σ) : iProp Σ :=
    (∀ a, {{{ Ψ1 a }}} v (f a) ?{{{ a, RET f a; Ψ2 a }}})%I.

  Global Instance is_mon_persistent v Ψ1 Ψ2 :
    PersistentP (is_mon v Ψ1 Ψ2).
  Proof. apply _. Qed.
  Global Instance is_mon_ne v n :
     Proper (ext (dist n) ==> ext (dist n) ==> dist n) (is_mon v).
  Proof. solve_proper. Qed.
  Global Instance is_mon_proper v :
     Proper (ext (≡) ==> ext (≡) ==> (≡)) (is_mon v).
  Proof. solve_proper. Qed.
End is_mon.
Typeclasses Opaque is_mon.

(** * Membrane proof *)

Section proof.
  Import notation.
  Context `{heapG Σ} (locin locout : val) (Ψ : loc → iProp Σ).
  Context {HΨ : ∀ l, PersistentP (Ψ l)}.
  Notation of_loc := (λ l : loc, #l).

  Lemma wrap_unwrap :
    is_mon of_loc locout Ψ low -∗
    is_mon of_loc locin low Ψ -∗
    □ ((∀ p E Φ, ▷(∀ v, is_mon id v (on_val Ψ) low -∗ Φ v) -∗
      WP membrane locout locin @ p; E {{ Φ }}) ∗
     (∀ p E Φ, ▷(∀ v, is_mon id v low (on_val Ψ) -∗ Φ v) -∗
      WP membrane locin locout @ p; E {{ Φ }}))%I.
  Proof.
    iIntros "#Hlocout #Hlocin".
    iLöb as "IH". iDestruct "IH" as "#(IHmkw & IHmku)".
      do 2!rewrite -always_later always_elim. iAlways.
    iSplitL.
    - iIntros (p E Φ) "HΦ". wp_rec. wp_lam.
      iApply "HΦ". clear Φ. iIntros (v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
      wp_apply "IHmkw". iIntros (wrap) "#Hwrap". iClear "IHmkw".
        rewrite {4}/is_mon. setoid_rewrite always_elim. wp_let.

      (* Wrapping functions. *)
      wp_typecast Hrec.
      + iClear "Hlocout Hlocin".
        (* Unfold Hv early, to eat the later. *)
        destruct (is_rec_val _ Hrec) as (f&x&erec&?&->).
          rewrite on_val_elim always_elim. wp_match.
        wp_apply "IHmku". iIntros (unwrap) "#Hunwrap". iClear "IHmku".
          rewrite/is_mon. wp_let.
        iApply "HΦ". clear Φ.
        rewrite low_val. iAlways. iNext. iIntros (v1 Φ) "Hv1 HΦ".
          simpl_subst.
        wp_apply ("Hunwrap" with "* [$Hv1]"). iIntros (v2) "Hv2". wp_rec.
        wp_apply ("Hv" with "[$Hv2]"). iIntros (v3) "Hv3".
        by wp_apply ("Hwrap" with "* [$Hv3]").
      wp_match. iClear "IHmku Hlocin".

      (* Wrapping literals. *)
      wp_typecast Hlit; wp_match.
      + iClear "Hwrap".

        (* Wrapping locations. *)
        wp_typecast Hloc; wp_match.
        * destruct (is_loc_val _ Hloc) as (l&->).
            rewrite on_val_elim on_lit_elim /is_mon.
          wp_apply ("Hlocout" with "* [$Hv]"). iIntros (v1) "Hv1".
          iApply "HΦ". by rewrite low_val low_lit.

        (* Wrapping other literals. *)
        iApply "HΦ". destruct (is_lit_val _ Hlit) as (lit&HV).
          rewrite HV low_val low_lit. rewrite HV /is_loc in Hloc.
        case: lit Hloc {Hlit HV} => // l Hloc. by exfalso; eauto.
      iClear "Hlocout".

      (* Wrapping pairs. *)
      wp_typecast Hp.
      + (* Unfold Hv early, to eat the later. *)
        destruct (is_pair_val _ Hp) as (v1&v2&->).
          iDestruct "Hv" as "#(Hv1 & Hv2)". wp_match. wp_proj.
        wp_apply ("Hwrap" with "* [$Hv1]"). iIntros (v'1) "Hv'1". wp_let.
          wp_proj.
        wp_apply ("Hwrap" with "* [$Hv2]"). iIntros (v'2) "Hv'2". wp_let.
        iApply "HΦ". rewrite (low_val (PairV _ _)). by iFrame.
      wp_match.

      (* Wrapping left injections. *)
      wp_typecast v0 Hinl.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinl. wp_match.
        wp_apply ("Hwrap" with "* [$Hv]"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (low_val (InjLV _)). by iFrame.
      wp_match.

      (* Wrapping right injections. *)
      wp_typecast v0 Hinr.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinr. wp_match.
        wp_apply ("Hwrap" with "* [$Hv]"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (low_val (InjRV _)). by iFrame.
      wp_match.
      iExFalso. iPureIntro. exact: is_val_exhaustive.

    - iIntros (p E Φ) "HΦ". wp_rec. wp_lam.
      iApply "HΦ". clear Φ. iIntros (v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
      wp_apply "IHmku". iIntros (unwrap) "#Hunwrap". iClear "IHmku".
        rewrite {4}/is_mon. setoid_rewrite always_elim. wp_let.

      (* Unwrapping functions. *)
      wp_typecast Hrec.
      + iClear "Hlocout Hlocin".
        (* Unfold Hv early, to eat the later. *)
        destruct (is_rec_val v Hrec) as (f&x&erec&?&->).
          rewrite low_val always_elim. wp_match.
        wp_apply "IHmkw". iIntros (wrap) "#Hwrap". iClear "IHmkw".
          rewrite/is_mon. wp_let.
        iApply "HΦ". clear Φ.
        rewrite on_val_elim. iAlways. iNext. iIntros (v1 Φ) "Hv1 HΦ".
          simpl_subst.
        wp_apply ("Hwrap" with "* [$Hv1]"). iIntros (v2) "Hv2". wp_rec.
        wp_apply ("Hv" with "[$Hv2]"). iIntros (v3) "Hv3".
        by wp_apply ("Hunwrap" with "* [$Hv3]").
      wp_match. iClear "IHmkw Hlocout".

      (* Unwrapping literals. *)
      wp_typecast Hlit; wp_match.
      + iClear "Hunwrap".

        (* Unwrapping locations. *)
        wp_typecast Hloc; wp_match.
        * destruct (is_loc_val _ Hloc) as (l1&->).
            rewrite low_val low_lit /is_mon.
          wp_apply ("Hlocin" with "* [$Hv]"). iIntros (l2) "Hl2".
          iApply "HΦ". rewrite on_val_elim on_lit_elim. by iFrame.

        (* Unwrapping other literals. *)
        iApply "HΦ". destruct (is_lit_val _ Hlit) as (lit&HV).
          rewrite HV low_val on_val_elim on_lit_elim.
          rewrite HV /is_loc in Hloc.
        case: lit Hloc {Hlit HV} => //= l Hloc. by exfalso; eauto.
      iClear "Hlocin".

      (* Unwrapping pairs. *)
      wp_typecast Hp.
      + (* Unfold Hv early, to eat the later. *)
        destruct (is_pair_val _ Hp) as (v1&v2&->).
          iDestruct "Hv" as "#(Hv1 & Hv2)". wp_match. wp_proj.
        wp_apply ("Hunwrap" with "* [$Hv1]"). iIntros (v'1) "Hv'1". wp_let.
          wp_proj.
        wp_apply ("Hunwrap" with "* [$Hv2]"). iIntros (v'2) "Hv'2". wp_let.
        iApply "HΦ". rewrite (on_val_elim _ (PairV _ _)). by iFrame.
      wp_match.

      (* Unwrapping left injections. *)
      wp_typecast v0 Hinl.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinl. wp_match.
        wp_apply ("Hunwrap" with "* [$Hv]"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (on_val_elim _ (InjLV _)). by iFrame.
      wp_match.

      (* Unwrapping right injections. *)
      wp_typecast v0 Hinr.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinr. wp_match.
        wp_apply ("Hunwrap" with "* [$Hv]"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (on_val_elim _ (InjRV _)). by iFrame.
      wp_match.
      iExFalso. iPureIntro. exact: is_val_exhaustive.
  Qed.

  (**
	The membrane lifts reference monitors (of type [Ψ ↔ low]) on
	locations to reference monitors (of type [on_val Ψ → low]) on
	values.
  *)
  Lemma membrane_spec p E :
    {{{ is_mon of_loc locout Ψ low ∗ is_mon of_loc locin low Ψ }}}
      membrane locout locin @ p; E
    {{{ wrap, RET wrap; is_mon id wrap (on_val Ψ) low }}}.
  Proof.
    iIntros (Φ) "[Hout Hin] HΦ".
    iDestruct (wrap_unwrap with "[$Hout] [$Hin]") as "(Hw & _)".
    by iApply "Hw".
  Qed.
End proof.

(**
	When [locout] works unconditionally, the membrane can wrap all
	_inert_ values. Inert values (i) include all base values and
	(ii) are closed under function abstraction, pairing, and
	injections. Inert locations cannot be used to inspect or
	modify the heap; otherwise, eliminating an inert value
	produces an inert value.

	Examples:

	[λ _, ℓ] is inert, whether location ℓ is high or low

	[λ x, assert (x = 1)] is not inert because, if x is any inert
	value, there is no way to prove x = 1

	[λ x, ! x] is not inert because inert locations cannot inspect
	the heap

	[λ x, assume (x = ℓ); ! x; ()] is inert (assuming, say, a
	suitable invariant about location ℓ)
*)
Section inert.
  Context `{heapG Σ}.
  Implicit Types l : loc.
  Implicit Types v : val.
  Import notation.

  Definition inert : val → iProp Σ := on_val (const True%I).
  Definition is_locout (locout : val) : iProp Σ :=
    (∀ l1, {{{ True }}} locout #l1 ?{{{ l2, RET #l2; low l2 }}})%I.
  Definition is_locin (locin : val) : iProp Σ :=
    (∀ l2, {{{ low l2 }}} locin #l2 ?{{{ l1, RET #l1; True }}})%I.
  Definition is_wrap (wrap : val) : iProp Σ :=
    (∀ v1, {{{ inert v1 }}} wrap v1 ?{{{ v2, RET v2; low v2 }}})%I.

  Lemma inert_membrane_spec p E locout locin :
    {{{ is_locout locout ∗ is_locin locin }}}
      membrane locout locin @ p; E
    {{{ wrap, RET wrap; is_wrap wrap }}}.
  Proof.
    iIntros (Φ) "#(Hout & Hin)". rewrite -membrane_spec. clear Φ. iSplit.
    - iIntros (l) "!#". iIntros (Φ) "_ HΦ".
      by iApply ("Hout" $! l with "[] [$HΦ]").
    - iIntros (l) "!#". iIntros (Φ) "Hl HΦ".
      by iApply ("Hin" $! l with "[$Hl] [$HΦ]").
  Qed.
End inert.
