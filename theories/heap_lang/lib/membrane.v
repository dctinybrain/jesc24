From iris.heap_lang Require Export heap.
From iris.heap_lang Require notation.
From iris.heap_lang.lib Require Export monitor.
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
    else ifloc: "x" as "l" => "locout" "l"
    else iflit: "x" as "lit" => "lit"
    else if: "x" = () then ()
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

(** * Membrane proof *)

Section proof.
  Import notation.
  Context `{heapG Σ} (locout locin : val).
  Context (Ψ : loc → iProp Σ) {HΨ : ∀ l, PersistentP (Ψ l)}.

  Notation lowval := (low : val → iProp Σ).

  Lemma wrap_unwrap p1 p2 :
    is_monP p1 locout Ψ low -∗
    is_monP p2 locin low Ψ -∗
    □ ((∀ p E Φ, ▷(∀ v, is_monP p1 v (on_val Ψ) lowval -∗ Φ v) -∗
      WP membrane locout locin @ p; E {{ Φ }}) ∗
     (∀ p E Φ, ▷(∀ v, is_monP p2 v lowval (on_val Ψ) -∗ Φ v) -∗
      WP membrane locin locout @ p; E {{ Φ }}))%I.
  Proof.
    iIntros "#Hlocout #Hlocin".
    iLöb as "IH". iDestruct "IH" as "#(IHmkw & IHmku)".
      do 2!rewrite -always_later always_elim. iAlways.
    iSplitL.
    - iIntros (p E Φ) "HΦ". wp_rec. wp_lam.
      iApply "HΦ". clear Φ. iIntros (v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
      wp_apply "IHmkw". iIntros (wrap) "#Hwrap". iClear "IHmkw".
        rewrite (monP_triple _ wrap). setoid_rewrite always_elim.
        wp_let.

      (* Wrapping functions. *)
      wp_typecast Hrec.
      + iClear "Hlocout Hlocin".
        (* Unfold Hv early, to eat the later. *)
        destruct (is_rec_val _ Hrec) as (f&x&erec&?&->).
          rewrite on_val_rec always_elim. wp_match.
        wp_apply "IHmku". iIntros (unwrap) "#Hunwrap". iClear "IHmku".
          rewrite (monP_triple _ unwrap).
          setoid_rewrite (wp_forget_progress p2).
          wp_let.
        iApply "HΦ". clear Φ.
        rewrite low_val. iAlways. iNext. iIntros (v1) "Hv1".
          simpl_subst.
        wp_apply ("Hunwrap" with "* Hv1"). iIntros (v2) "Hv2". wp_rec.
        wp_apply ("Hv" with "Hv2"). iIntros (v3) "Hv3".
          setoid_rewrite (wp_forget_progress p1 _ (wrap _)).
        wp_apply ("Hwrap" with "* Hv3"). by iIntros.
      wp_match. iClear "IHmku Hlocin".

      (* Wrapping locations. *)
      wp_typecast Hloc; wp_match.
      + destruct (is_loc_val _ Hloc) as (l&->).
          rewrite on_val_elim (monP_triple _ locout).
        wp_apply ("Hlocout" with "* Hv"). iIntros (v1) "Hv1".
        iApply "HΦ". by rewrite low_val.
      iClear "Hlocout".

      (* Wrapping literals. *)
      wp_typecast Hlit; wp_match.
      + iApply "HΦ". destruct (is_lit_val _ Hlit) as (lit&->).
        by rewrite low_val.

      (* Wrapping unit. *)
      wp_op=>Hu; wp_if.
      + iApply "HΦ". by rewrite low_val.

      (* Wrapping pairs. *)
      wp_typecast Hp.
      + (* Unfold Hv early, to eat the later. *)
        destruct (is_pair_val _ Hp) as (v1&v2&->).
          iDestruct "Hv" as "#(Hv1 & Hv2)". wp_match. wp_proj.
        wp_apply ("Hwrap" with "* Hv1"). iIntros (v'1) "Hv'1". wp_let.
          wp_proj.
        wp_apply ("Hwrap" with "* Hv2"). iIntros (v'2) "Hv'2". wp_let.
        iApply "HΦ". rewrite (low_val (PairV _ _)). by iFrame.
      wp_match.

      (* Wrapping left injections. *)
      wp_typecast v0 Hinl.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinl. wp_match.
        wp_apply ("Hwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (low_val (InjLV _)). by iFrame.
      wp_match.

      (* Wrapping right injections. *)
      wp_typecast v0 Hinr.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinr. wp_match.
        wp_apply ("Hwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (low_val (InjRV _)). by iFrame.
      wp_match.

      (* We're done with wrapping. *)
      iExFalso. iPureIntro.
      apply (is_val_exhaustive v); auto using of_val_inj.

    - iIntros (p E Φ) "HΦ". wp_rec. wp_lam.
      iApply "HΦ". clear Φ. iIntros (v) "!#". iIntros (Φ) "#Hv HΦ". wp_lam.
      wp_apply "IHmku". iIntros (unwrap) "#Hunwrap". iClear "IHmku".
        rewrite (monP_triple _ unwrap). setoid_rewrite always_elim.
        wp_let.

      (* Unwrapping functions. *)
      wp_typecast Hrec.
      + iClear "Hlocout Hlocin".
        (* Unfold Hv early, to eat the later. *)
        destruct (is_rec_val v Hrec) as (f&x&erec&?&->).
          rewrite low_rec always_elim. wp_match.
        wp_apply "IHmkw". iIntros (wrap) "#Hwrap". iClear "IHmkw".
          rewrite (monP_triple _ wrap).
          setoid_rewrite (wp_forget_progress p1 _ (wrap _)).
          wp_let.
        iApply "HΦ". clear Φ.
        rewrite on_val_elim. iAlways. iNext. iIntros (v1) "Hv1".
          simpl_subst.
        wp_apply ("Hwrap" with "* Hv1"). iIntros (v2) "Hv2". wp_rec.
        wp_apply ("Hv" with "Hv2"). iIntros (v3) "Hv3".
          setoid_rewrite (wp_forget_progress p2 _ (unwrap _)).
        wp_apply ("Hunwrap" with "* Hv3"). by iIntros.
      wp_match. iClear "IHmkw Hlocout".

      (* Unwrapping locations. *)
      wp_typecast Hloc; wp_match.
      + destruct (is_loc_val _ Hloc) as (l1&->).
          rewrite low_val (monP_triple _ locin).
        wp_apply ("Hlocin" with "* Hv"). iIntros (l2) "Hl2".
        iApply "HΦ". rewrite on_val_elim. by iFrame.
      iClear "Hlocin".

      (* Unwrapping literals. *)
      wp_typecast Hlit; wp_match.
      + iApply "HΦ". destruct (is_lit_val _ Hlit) as (lit&->).
        by rewrite on_val_elim.

      (* Unwapping unit. *)
      wp_op=>Hu; wp_if.
      + iApply "HΦ". by rewrite on_val_elim.

      (* Unwrapping pairs. *)
      wp_typecast Hp.
      + (* Unfold Hv early, to eat the later. *)
        destruct (is_pair_val _ Hp) as (v1&v2&->).
          iDestruct "Hv" as "#(Hv1 & Hv2)". wp_match. wp_proj.
        wp_apply ("Hunwrap" with "* Hv1"). iIntros (v'1) "Hv'1". wp_let.
          wp_proj.
        wp_apply ("Hunwrap" with "* Hv2"). iIntros (v'2) "Hv'2". wp_let.
        iApply "HΦ". rewrite (on_val_elim _ (PairV _ _)). by iFrame.
      wp_match.

      (* Unwrapping left injections. *)
      wp_typecast v0 Hinl.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinl. wp_match.
        wp_apply ("Hunwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (on_val_elim _ (InjLV _)). by iFrame.
      wp_match.

      (* Unwrapping right injections. *)
      wp_typecast v0 Hinr.
      + (* Unfold Hv early, to eat the later. *)
        rewrite Hinr. wp_match.
        wp_apply ("Hunwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
        iApply "HΦ". rewrite (on_val_elim _ (InjRV _)). by iFrame.
      wp_match.

      (* We're done with unwrapping. *)
      iExFalso. iPureIntro.
      apply (is_val_exhaustive v); auto using of_val_inj.
  Qed.

  (**
	The membrane lifts reference monitors (of type [Ψ ↔ low]) on
	locations to reference monitors (of type [on_val Ψ → low]) on
	values.
  *)
  Lemma membrane_wrap_spec p E p1 p2 :
    {{{ is_monP p1 locout Ψ low ∗ is_monP p2 locin low Ψ }}}
      membrane locout locin @ p; E
    {{{ wrap, RET wrap; is_monP p1 wrap (on_val Ψ) lowval }}}.
  Proof.
    iIntros (Φ) "[Hout Hin] HΦ".
    iDestruct (wrap_unwrap with "Hout Hin") as "(Hw & _)".
    by iApply "Hw".
  Qed.

  Lemma membrane_unwrap_spec p E p1 p2 :
    {{{ is_monP p1 locout Ψ low ∗ is_monP p2 locin low Ψ }}}
      membrane locin locout @ p; E
    {{{ unwrap, RET unwrap; is_monP p2 unwrap lowval (on_val Ψ) }}}.
  Proof.
    iIntros (Φ) "[Hout Hin] HΦ".
    iDestruct (wrap_unwrap with "Hout Hin") as "(_ & Hu)".
    by iApply "Hu".
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
  Notation lowval := (low : val → iProp Σ).

  Definition inert : val → iProp Σ := on_val (const True%I).

  Definition is_locout (p1 : pbit) (locout : val) : iProp Σ :=
    is_monP p1 locout (const True%I) low.
  Definition is_locin (p2 : pbit) (locin : val) : iProp Σ :=
    is_monP p2 locin lowloc (const True%I).
  Definition is_wrap (p1 : pbit) (wrap : val) : iProp Σ :=
    is_monP p1 wrap inert lowval.
  Definition is_unwrap (p2 : pbit) (unwrap : val) : iProp Σ :=
    is_monP p2 unwrap lowval inert.

  Lemma locout_triple p1 locout :
    is_locout p1 locout ⊣⊢
    (∀ l1, {{{ True }}} locout l1 @ p1; ⊤ {{{ l2, RET LocV l2; low l2 }}})%I.
  Proof. by []. Qed.

  Lemma locin_triple p2 locin :
    is_locin p2 locin ⊣⊢
    (∀ l2, {{{ low l2 }}} locin l2 @ p2; ⊤ {{{ l1, RET LocV l1; True }}})%I.
  Proof. by []. Qed.

  Lemma wrap_triple p1 wrap :
    is_wrap p1 wrap ⊣⊢
    (∀ v1, {{{ inert v1 }}} wrap v1 @ p1; ⊤ {{{ v2, RET v2; low v2 }}})%I.
  Proof. by []. Qed.

  Lemma unwrap_triple p2 unwrap :
    is_unwrap p2 unwrap ⊣⊢
    (∀ v2, {{{ low v2 }}} unwrap v2 @ p2; ⊤ {{{ v1, RET v1; inert v1 }}})%I.
  Proof. by []. Qed.

  Lemma inert_wrap_spec p E locout locin p1 p2 :
    {{{ is_locout p1 locout ∗ is_locin p2 locin }}}
      membrane locout locin @ p; E
    {{{ wrap, RET wrap; is_wrap p1 wrap }}}.
  Proof.
    iIntros (Φ) "#(?&?)". rewrite -membrane_wrap_spec. by iSplit.
  Qed.

  Lemma inert_unwrap_spec p E locout locin p1 p2 :
    {{{ is_locout p1 locout ∗ is_locin p2 locin }}}
      membrane locin locout @ p; E
    {{{ unwrap, RET unwrap; is_unwrap p2 unwrap }}}.
  Proof.
    iIntros (Φ) "#(?&?)". rewrite -membrane_unwrap_spec. by iSplit.
  Qed.
End inert.
