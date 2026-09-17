import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreak
import Mathlib.Tactic

/-!
# Complete lower-ray facet endpoint rank-two frontier

The endpoint rank-two reduction leaves only three pure transverse powers.
Each such power now has an honest positive source exposure and reverse-Rees
first-break package.  This file packages those two outcomes without claiming
that auxiliary first-break geometry is itself an actual-state Hessian chart.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Source-honest first-break package for a pure lower-ray facet endpoint. -/
structure QsRayFacetEndpointFirstBreakData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  exposure : QsRayFacetEndpointSourceExposure C
  activeCoordinate : Fin 4
  kernelCoordinate : Fin 4
  active_ne_kernel : activeCoordinate ≠ kernelCoordinate
  active_two_le : 2 ≤ C.ray.facetExponent activeCoordinate
  kernel_zero : C.ray.facetExponent kernelCoordinate = 0

namespace QsRayFacetEndpointFirstBreakData

/-- The retained package carries concrete rank-two geometry at the first actual
opening of the absent Hessian row. -/
theorem firstBreakRankTwoOutcome
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (D : QsRayFacetEndpointFirstBreakData C) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  exact D.exposure.firstBreakRankTwoOutcome
    D.activeCoordinate D.kernelCoordinate D.active_ne_kernel
    D.active_two_le D.kernel_zero

end QsRayFacetEndpointFirstBreakData

/-- **Complete lower-ray facet endpoint rank-two frontier.**  Every nonlinear
`.qs` facet endpoint either gives an actual represented-source rank-two chart
immediately, or a source-honest first-break package with concrete rank-two
geometry on its auxiliary Rees family. -/
theorem qs_ray_facetEndpoint_actualRankTwo_or_firstBreak
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty (QsRayFacetEndpointFirstBreakData C) := by
  rcases C.qs_ray_facetEndpoint_actualRankTwo_or_pureAxis with
    htwo | h1 | h2 | h3
  · exact Or.inl htwo
  · rcases C.exists_qs_ray_facetEndpoint_sourceExposure with ⟨E⟩
    exact Or.inr ⟨{
      exposure := E
      activeCoordinate := (1 : Fin 4)
      kernelCoordinate := (2 : Fin 4)
      active_ne_kernel := by decide
      active_two_le := by omega
      kernel_zero := h1.2.2.1
    }⟩
  · rcases C.exists_qs_ray_facetEndpoint_sourceExposure with ⟨E⟩
    exact Or.inr ⟨{
      exposure := E
      activeCoordinate := (2 : Fin 4)
      kernelCoordinate := (1 : Fin 4)
      active_ne_kernel := by decide
      active_two_le := by omega
      kernel_zero := h2.2.2.1
    }⟩
  · rcases C.exists_qs_ray_facetEndpoint_sourceExposure with ⟨E⟩
    exact Or.inr ⟨{
      exposure := E
      activeCoordinate := (3 : Fin 4)
      kernelCoordinate := (1 : Fin 4)
      active_ne_kernel := by decide
      active_two_le := by omega
      kernel_zero := h3.2.2.1
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
