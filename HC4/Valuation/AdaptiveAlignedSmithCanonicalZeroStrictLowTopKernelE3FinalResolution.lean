import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRelativeSourceRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution

/-!
# E3: exact final-resolution obligations for the top-kernel linear-power seam

The marked-axis E1/E2 analysis and the source-honest C/D analysis have now
been completely compressed.  Every retained linear-power top-kernel packet
reaches exactly one of two represented-source rank-three Hessian events:

* an evaluated nonzero source 3x3 Hessian minor; or
* a nonzero constant 3x3 Hessian minor on an honest exact-active source chart.

Neither event is, by itself, a terminal contradiction.  The only remaining
mathematics is to turn each event into one of the already-permitted
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution`
constructors.

This file records precisely those two extraction obligations and proves the
mechanical E1/E2/E3 assembly around them.  No new final-resolution constructor,
repair label, or terminal endpoint is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The exact two polynomial-level extraction obligations left after the
linear-power E3 source-rank-three collapse. -/
structure TopKernelLinearPowerE3FinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourcePoint :
    P.PositiveTailRepresentedSourceThreeByThreePointGeometry →
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- **Top-kernel E1/E2/E3 assembly.**

Once the two genuine source-rank-three events can be converted to permitted
polynomial endpoints, every linear-power top-kernel packet has a sound final
resolution.  All marked-axis support cases, cross-facet/codimension-two
branches, projected Schur cases and relative-order cases have already been
consumed upstream. -/
theorem exists_finalResolution_of_e3Extractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3FinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  rcases E.toE3RankThreeFrontier with ⟨G⟩
  cases G with
  | sourcePointThreeByThree Q =>
      exact X.sourcePoint Q
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
