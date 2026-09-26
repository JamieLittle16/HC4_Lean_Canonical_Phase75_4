import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceHomogeneous
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.55: balance-free boundary frontier for the zero strict-low terminal

A19.54 places the genuine zero-clock strict-low blocker packet on the same
represented state as the nonzero nonlinear Hessian-singular maximal ordinary
top face.  A18.5.92--93 require no torus grading: every such singular nonlinear
polynomial exposes an actual coordinate-boundary vertex, and in four variables
that vertex is either rank three on one coordinate facet or lies on a
codimension-two coordinate boundary.

This file is therefore only an adapter.  It introduces no new support or
homogeneity hypothesis and keeps the full A19.49--52 strict-low provenance
attached to the resulting Newton boundary split.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The actual singular top face of an A19.54 terminal has a balance-free
exposed nonlinear coordinate-boundary vertex. -/
noncomputable def exposedSingularBoundaryVertex
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    ExposedSingularNonlinearBoundaryVertexData T.topFace.face :=
  HC4.Newton.exposedSingularNonlinearBoundaryVertex
    T.topFace.face
    T.topFace.face_ne_zero
    T.topFace.hessian_zero
    T.topFace.face_support_degree_ge_three

/-- **A19.55 balance-free terminal boundary split.**

The remaining zero-clock strict-low terminal exposes either an actual
rank-three coordinate-facet exponent or an actual codimension-two boundary
exponent.  No symmetric torus balance or terminal cocharacter is assumed. -/
theorem exposedBoundary_rankThreeFacet_or_codimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ facet : ToricFacet,
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent) ∨
      MvExponentOnCodimensionTwoBoundary
        T.exposedSingularBoundaryVertex.exponent :=
  T.exposedSingularBoundaryVertex.rankThreeFacet_or_codimensionTwo

/-- The exposed boundary exponent remains genuinely nonlinear. -/
theorem exposedBoundary_exponent_degree_ge_three
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    3 ≤ HC4.Polynomial.ordinaryDegree4
      T.exposedSingularBoundaryVertex.exponent :=
  T.exposedSingularBoundaryVertex.exponent_nonlinear

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Upgrade the producer-free global/local split all the way to an explicit
balance-free Newton boundary carrier. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_zeroStrictLowBoundaryTerminal
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
          (K := K) T.trace.reachedRankThree.state) :=
  T.globalProgress_or_zeroStrictLowSingularTerminal hsrepair

end

end HC4.Valuation
