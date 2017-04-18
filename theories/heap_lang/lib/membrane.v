From iris.heap_lang Require Export heap.
From iris.heap_lang Require Import notation.
From iris.heap_lang.lib Require Export monitor.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
Import uPred.

Set Bullet Behavior "None".

(** * Membrane code *)
(**
	The membrane constructs values that may be safely shared with
	adversarial code (i.e., values in [lowval ≡ on_val lowloc]).

	To read the code, it helps to have a spec in mind. Roughly,
	our specification says that if [locout : Ψ1 → Ψ2] and [locin :
	Ψ2 → Ψ1] for some "types" [Ψ1, Ψ2] of locations, then
	[membrane locout locin : on_val Ψ1 → on_val Ψ2]; that is, the
	membrane lifts reference monitors for locations to reference
	monitors for values. See [membrane_spec] and the special case
	[inert_wrap_spec, inert_unwrap_spec].
*)
Section code.
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
  Context `{heapG Σ}.
  Implicit Types f g : val.

  Lemma membrane_spec p0 E0 p1 vout  Ψ1 Ψ2
      {HΨ1 : ∀ l, PersistentP (Ψ1 l)} {HΨ2 : ∀ l, PersistentP (Ψ2 l)} :
    {{{ is_monP p1 vout Ψ1 Ψ2 }}}
      membrane vout @ p0; E0
    {{{ f, RET f; ∀ p0 E0 p2 vin,
      {{{ is_monP p2 vin Ψ2 Ψ1 }}} f vin @ p0; E0 {{{ g, RET g;
        is_monP p1 g (on_val Ψ1) (on_val Ψ2)
      }}}
    }}}%I.	(* %I as the iLöb tactic cannot generalize 9 variables *)
  Proof.
    (**
      A straightforward Löb induction, unfolding our assumption
      [on_val Ψ1 v] early when [v] is a function, pair, or injection
      (in order to eat the later exposed by unfolding).
    *)
    iAlways. iLöb as "IH" forall (p0 E0 p1 vout Ψ1 Ψ2 HΨ1 HΨ2).
      iIntros (Φ) "#Hout HΦ". wp_rec.
    iApply "HΦ". clear p0 E0 Φ. iIntros (p0 E0 p2 vin) "!#".
      iIntros (Φ) "#Hin HΦ". wp_lam.
    iApply "HΦ". clear p0 E0 Φ. iIntros (v) "!#". iIntros (Φ) "#Hv HΦ". wp_let.
    wp_apply ("IH" $! _ _ _ _ Ψ1 Ψ2 with "[%] [%] * Hout"). iIntros (w) "Hw".
    wp_apply ("Hw" with "* Hin"). clear w. iIntros (wrap) "#Hwrap". wp_let.

    (* Wrapping functions. *)
    wp_typecast Hrec.
    - destruct (is_rec_val _ Hrec) as (f&x&erec&?&->).
        rewrite on_val_rec always_elim. wp_match.
      wp_apply ("IH" $! _ _ _ _ Ψ2 Ψ1 with "[%] [%] * Hin"). iIntros (u) "Hu".
      wp_apply ("Hu" with "* Hout"). iClear (u) "IH Hout Hin".
        iIntros (unwrap) "#Hunwrap". wp_let.
      iApply "HΦ". clear Φ.
      rewrite on_val_elim. iAlways. iNext. iIntros (v1) "Hv1".
        simpl_subst. rewrite (monP_pbit_mono noprogress p2) //
          (monP_triple _ unwrap).
      wp_apply ("Hunwrap" with "* Hv1"). iIntros (v2) "Hv2". wp_rec.
      wp_apply ("Hv" with "Hv2"). iIntros (v3) "Hv3".
        rewrite (monP_pbit_mono noprogress p1) //
          (monP_triple _ wrap).
      wp_apply ("Hwrap" with "* Hv3"). by iIntros.
    wp_match. iClear "IH Hin".

    (* Wrapping locations. *)
    wp_typecast Hloc; wp_match.
    - destruct (is_loc_val _ Hloc) as (l&->).
        rewrite on_val_elim (monP_triple _ vout).
      wp_apply ("Hout" with "* Hv"). iIntros (v1) "Hv1".
      iApply "HΦ". by rewrite on_val_elim.
    iClear "Hout".

    (* Wrapping literals. *)
    wp_typecast Hlit; wp_match.
    - iApply "HΦ". destruct (is_lit_val _ Hlit) as (lit&->).
      by rewrite (on_val_elim Ψ2 _).

    (* Wrapping unit. *)
    wp_op=>Hu; wp_if.
    - iApply "HΦ". by rewrite (on_val_elim Ψ2 _).
    rewrite monP_triple.

    (* Wrapping pairs. *)
    wp_typecast Hp.
    - destruct (is_pair_val _ Hp) as (v1&v2&->).
        iDestruct "Hv" as "#(Hv1 & Hv2)". wp_match. wp_proj.
      wp_apply ("Hwrap" with "* Hv1"). iIntros (v'1) "Hv'1". wp_let.
        wp_proj.
      wp_apply ("Hwrap" with "* Hv2"). iIntros (v'2) "Hv'2". wp_let.
      iApply "HΦ". rewrite (on_val_elim _ (PairV _ _)). by iFrame.
    wp_match.

    (* Wrapping left injections. *)
    wp_typecast v0 Hinl.
    - rewrite Hinl. wp_match.
      wp_apply ("Hwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
      iApply "HΦ". rewrite (on_val_elim _ (InjLV _)). by iFrame.
    wp_match.

    (* Wrapping right injections. *)
    wp_typecast v0 Hinr.
    - rewrite Hinr. wp_match.
      wp_apply ("Hwrap" with "* Hv"). iIntros (v1) "Hv1". wp_value.
      iApply "HΦ". rewrite (on_val_elim _ (InjRV _)). by iFrame.
    wp_match.
    iExFalso. iPureIntro.
    apply (is_val_exhaustive v); auto using of_val_inj.
  Qed.
End proof.

(** * Special case: Membrane for inert values *)

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
  Implicit Types f g : val.

  Lemma inert_wrap_spec p0 E0 p1 vout :
    {{{ is_monP p1 vout (const True) low }}}
      membrane vout @ p0; E0
    {{{ f, RET f; ∀ p0 E0 p2 vin,
      {{{ is_monP p2 vin low (const True) }}} f vin @ p0; E0 {{{ g, RET g;
        is_monP p1 g (on_val (const True)) lowval
      }}}
    }}}.
  Proof.
    iIntros (Φ) "Hout HΦ".
    wp_apply (membrane_spec with "Hout"). iIntros (w) "#Hw".
    iApply "HΦ". clear p0 E0 Φ. iIntros (p0 E0 p2 vin) "!#".
      iIntros (Φ) "Hin HΦ".
    by wp_apply ("Hw" with "* Hin").
  Qed.

  Lemma inert_unwrap_spec p0 E0 p2 vin :
    {{{ is_monP p2 vin low (const True) }}}
      membrane vin @ p0; E0
    {{{ f, RET f; ∀ p0 E0 p1 vout,
      {{{ is_monP p1 vout (const True) low }}} f vout @ p0; E0 {{{ g, RET g;
        is_monP p2 g lowval (on_val (const True))
      }}}
    }}}.
  Proof.
    iIntros (Φ) "Hin HΦ".
    wp_apply (membrane_spec with "Hin"). iIntros (u) "#Hu".
    iApply "HΦ". clear p0 E0 Φ. iIntros (p0 E0 p1 eout) "!#".
      iIntros (Φ) "Hout HΦ".
    by wp_apply ("Hu" with "* Hout").
  Qed.
End inert.
