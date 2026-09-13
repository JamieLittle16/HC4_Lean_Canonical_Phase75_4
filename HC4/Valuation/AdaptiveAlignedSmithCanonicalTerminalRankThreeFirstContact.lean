import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSingularCarrier
import HC4.Newton.FirstContactCrossFacetArithmetic
import HC4.Newton.FirstContactCrossFacetAffineRRImpossible
import Mathlib.Tactic

/-!
# A18.5.73: consume the terminal rank-three first-contact branch

A18.4.109 retains the genuine terminal state of the well-founded rank-one
trace, and A18.5.1--21 expose its represented special fibre without changing
presentation.  At a positive-defect terminal that special fibre is already
Hessian-singular.  The finite-support cross-facet constructor can therefore be
applied directly to the certified on-facet and off-facet support slices.

The original A18.5.72 arithmetic adapter remains available as the useful
intermediate statement `b = 1`.  The strengthened A18.5.73b affine terminal
argument now closes the same genuine rank-three first-contact branch outright,
without an integral reparameterisation or divisibility hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Original arithmetic form of the terminal `qs` rank-three first-contact
adapter.  It remains useful independently of the stronger direct
contradiction below. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.terminal_qs_rankThree_firstContact_forces_b_one
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    {a b contactScale contactBump : ℕ}
    {contactLevel : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (hfacet :
      (zeroCoordinateSupport (0 : Fin 4)
        trace.reachedPresentedRankThree.terminal.specialFiber).Nonempty)
    (hout :
      (positiveCoordinateSupport (0 : Fin 4)
        trace.reachedPresentedRankThree.terminal.specialFiber).Nonempty)
    (hBal : HC4.Polynomial.HasBalancedMvSupport a b
      trace.reachedPresentedRankThree.terminal.specialFiber)
    (hcontact : ∀ d ∈
        trace.reachedPresentedRankThree.terminal.specialFiber.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hrawDefect :
      0 < trace.reachedPresentedRankThree.terminal.presentedState.rawDefect)
    (hthree :
      MvRankThreeOnFacet .qs
        (crossFacetInitialData
          (i := crossFacetOppositeCoordinate (0 : Fin 4))
          hfacet hout).facetExponent) :
    b = 1 := by
  let D : CrossFacetInitialData
      trace.reachedPresentedRankThree.terminal.specialFiber
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4) :=
    crossFacetInitialData hfacet hout

  have hzero :
      HC4.Polynomial.hessianDeterminant
        trace.reachedPresentedRankThree.terminal.specialFiber = 0 := by
    simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
      using trace.reachedPresentedRankThree.terminal.presentedState.specialFiber_hessianDeterminant_eq_zero
        hrawDefect

  exact D.qs_rankThree_firstContact_forces_b_one
    ha hb hcop hcontactScale hcontactBump
    hBal hcontact hzero (by simpa [D] using hthree)

/-- **A18.5.73 — direct terminal first-contact contradiction.**

The same retained terminal data now enters the affine two-fixed endgame and
closes the rank-three `qs` first-contact branch outright.  Coprimality is not
needed for this stronger endpoint: the contradiction comes from the positive
first-contact degree drop and the affine RationalRigidity terminal identity. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.terminal_qs_rankThree_firstContact_impossible
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    {a b contactScale contactBump : ℕ}
    {contactLevel : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (hfacet :
      (zeroCoordinateSupport (0 : Fin 4)
        trace.reachedPresentedRankThree.terminal.specialFiber).Nonempty)
    (hout :
      (positiveCoordinateSupport (0 : Fin 4)
        trace.reachedPresentedRankThree.terminal.specialFiber).Nonempty)
    (hBal : HC4.Polynomial.HasBalancedMvSupport a b
      trace.reachedPresentedRankThree.terminal.specialFiber)
    (hcontact : ∀ d ∈
        trace.reachedPresentedRankThree.terminal.specialFiber.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hrawDefect :
      0 < trace.reachedPresentedRankThree.terminal.presentedState.rawDefect)
    (hthree :
      MvRankThreeOnFacet .qs
        (crossFacetInitialData
          (i := crossFacetOppositeCoordinate (0 : Fin 4))
          hfacet hout).facetExponent) :
    False := by
  let D : CrossFacetInitialData
      trace.reachedPresentedRankThree.terminal.specialFiber
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4) :=
    crossFacetInitialData hfacet hout

  have hzero :
      HC4.Polynomial.hessianDeterminant
        trace.reachedPresentedRankThree.terminal.specialFiber = 0 := by
    simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
      using trace.reachedPresentedRankThree.terminal.presentedState.specialFiber_hessianDeterminant_eq_zero
        hrawDefect

  exact D.qs_rankThree_firstContact_impossible
    ha hb hcontactScale hcontactBump
    hBal hcontact hzero (by simpa [D] using hthree)

end

end HC4.Valuation
