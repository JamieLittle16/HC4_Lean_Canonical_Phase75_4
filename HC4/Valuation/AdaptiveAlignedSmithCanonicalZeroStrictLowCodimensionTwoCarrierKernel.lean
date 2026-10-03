import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryFrontier
import HC4.Newton.FiniteSupportSingularBoundaryCarrierKernel
import Mathlib.Tactic

/-!
# A19.55 codimension-two branch retains a literal singular-carrier kernel

The balance-free A19.55 boundary split uses the canonical A18.5.92 exposed
vertex of the actual singular top face.  The canonical coordinate-max
constructor retains more geometry than the abstract codimension-two predicate
alone: on its stored exact singular carrier, one of the first three coordinate
partials vanishes identically.

This file is the source-facing adapter.  It keeps the result attached to the
actual zero-strict-low terminal and does not project the branch to generic
JC2.  It also does not manufacture repair progress; the next stage must study
the first honest opening of this literal carrier kernel.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The canonical A19.55 codimension-two exposed vertex comes with an exact
Hessian-singular carrier on which one actual coordinate direction is a literal
constant kernel. -/
theorem exposedCodimensionTwo_carrier_has_coordinateKernel
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hcodim : MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent) :
    ∃ i : Fin 3,
      MvPolynomial.pderiv (Fin.castSucc i)
        T.exposedSingularBoundaryVertex.carrier = 0 := by
  simpa [exposedSingularBoundaryVertex] using
    (HC4.Newton.exposedSingularNonlinearBoundaryVertex_carrier_has_coordinateKernel_of_codimensionTwo
      T.topFace.face
      T.topFace.face_ne_zero
      T.topFace.hessian_zero
      T.topFace.face_support_degree_ge_three
      hcodim)

/-- The carrier used by the preceding kernel statement is itself the honest
singular carrier retained by A18.5.92, not a synthetic polynomial. -/
theorem exposedCodimensionTwo_carrier_hessian_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (_hcodim : MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent) :
    HC4.Polynomial.hessianDeterminant
        T.exposedSingularBoundaryVertex.carrier = 0 :=
  T.exposedSingularBoundaryVertex.carrier_hessian_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
