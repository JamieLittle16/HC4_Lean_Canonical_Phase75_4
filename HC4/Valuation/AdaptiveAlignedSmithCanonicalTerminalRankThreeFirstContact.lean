import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSingularCarrier
import HC4.Newton.FirstContactCrossFacetArithmetic
import Mathlib.Tactic

/-!
# A18.5.73: consume the terminal rank-three first-contact branch

A18.4.109 retains the genuine terminal state of the well-founded rank-one
trace, and A18.5.1--21 expose its represented special fibre without changing
presentation.  At a positive-defect terminal that special fibre is already
Hessian-singular.  The finite-support cross-facet constructor can therefore be
applied directly to the certified on-facet and off-facet support slices.

This file is only the trace-facing adapter.  It does not re-prove first
contact, affine-line rigidity, or RationalRigidity.  Once the surviving `qs`
endpoint is rank three, A18.5.72 performs the entire arithmetic collapse.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A18.5.73 — terminal `qs` rank-three first-contact consumption.**

The finite rank-one trace supplies the actual represented terminal special
fibre.  Given the already-certified two support slices of the genuine first
contact, construct its exact `CrossFacetInitialData`.  Positive terminal defect
supplies Hessian singularity from the retained family, and A18.5.72 consumes
the surviving `qs` rank-three endpoint.

The remaining hypotheses are deliberately geometric certificates rather than
reconstructed algebra: terminal support/presentation adapters are expected to
supply them at the final splice. -/
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
    (hBal : HasBalancedMvSupport a b
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
      hessianDeterminant
        trace.reachedPresentedRankThree.terminal.specialFiber = 0 := by
    simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
      using trace.reachedPresentedRankThree.terminal.presentedState.specialFiber_hessianDeterminant_eq_zero
        hrawDefect

  exact D.qs_rankThree_firstContact_forces_b_one
    ha hb hcop hcontactScale hcontactBump
    hBal hcontact hzero (by simpa [D] using hthree)

end

end HC4.Valuation
