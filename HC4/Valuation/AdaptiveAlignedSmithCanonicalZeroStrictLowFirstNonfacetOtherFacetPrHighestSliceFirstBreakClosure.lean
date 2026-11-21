import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrHighestSliceFirstBreak
import Mathlib.Tactic

/-!
# Complete `.pr` highest-slice splice to honest rank-two geometry

The finite-staircase closure already sends every nontrivial `.pr` highest
slice, and every singleton with two positive coordinates, to an actual
rank-two Hessian chart on the represented state.  The only surviving shape is
therefore a pure coordinate power in coordinate `0` or `1`.

For that pure-axis survivor, the direct source exposure and honest reverse-Rees
family are already available.  We retain one active coordinate with exponent
at least two and one absent kernel coordinate, so the existing rank-one
special-fibre first-break theorem applies without any repair-only progress or
clock identification.

This file is deliberately only a splice layer.  It packages the source-honest
first-break data and derives the existing concrete rank-two first-break
outcome.
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

/-- Source-honest data for the only `.pr` highest-slice shape which does not
already give an actual rank-two chart on the represented special fibre. -/
structure QsOtherFacetPrHighestSliceFirstBreakData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  P : QsOtherFacetPlanarCarrierPackage C .pr
  S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P
  d : Fin 4 →₀ ℕ
  support_eq : S.slice.support = {d}
  exposure : QsOtherFacetPrHighestSliceSourceExposure P S
  activeCoordinate : Fin 4
  kernelCoordinate : Fin 4
  active_ne_kernel : activeCoordinate ≠ kernelCoordinate
  active_two_le : 2 ≤ d activeCoordinate
  kernel_zero : d kernelCoordinate = 0

namespace QsOtherFacetPrHighestSliceFirstBreakData

variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The retained pure-axis source exposure carries concrete rank-two geometry
at the first actual opening of its missing Hessian row. -/
theorem firstBreakRankTwoOutcome
    (D : QsOtherFacetPrHighestSliceFirstBreakData C) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
    let j := firstFourBlockKernelRowBreakOrder B hrow
    RankOneSpecialFiberFirstBreakOutcome B j := by
  exact D.exposure.singleton_firstBreakRankTwoOutcome
    D.support_eq D.activeCoordinate D.kernelCoordinate
    D.active_ne_kernel D.active_two_le D.kernel_zero

end QsOtherFacetPrHighestSliceFirstBreakData

/-- **Complete `.pr` highest-slice rank-two frontier.**  Every actual `.pr`
other-facet endpoint now gives either an actual rank-two Hessian chart on the
represented state immediately, or a source-honest reverse-Rees first-break
package whose first opening carries the concrete rank-two geometry of
`RankOneSpecialFiberFirstBreakOutcome`. -/
theorem qs_ray_pr_actualRankTwo_or_highestSliceFirstBreak
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty (QsOtherFacetPrHighestSliceFirstBreakData C) := by
  rcases C.qs_ray_pr_actualRankTwo_or_pureAxisHighestSlice
      hthree houtThree with htwo | hpure
  · exact Or.inl htwo
  · rcases hpure with ⟨P, S, d, hsupp, hpure⟩
    rcases S.exists_pr_sourceExposure with ⟨E⟩
    rcases hpure with hzero | hone
    · exact Or.inr ⟨{
        P := P
        S := S
        d := d
        support_eq := hsupp
        exposure := E
        activeCoordinate := (0 : Fin 4)
        kernelCoordinate := (2 : Fin 4)
        active_ne_kernel := by decide
        active_two_le := by omega
        kernel_zero := hzero.2.2.1
      }⟩
    · exact Or.inr ⟨{
        P := P
        S := S
        d := d
        support_eq := hsupp
        exposure := E
        activeCoordinate := (1 : Fin 4)
        kernelCoordinate := (2 : Fin 4)
        active_ne_kernel := by decide
        active_two_le := by omega
        kernel_zero := hone.2.2.1
      }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
