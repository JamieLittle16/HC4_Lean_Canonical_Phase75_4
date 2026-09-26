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

/-- **Single-obligation E3 extractor.**

At the actual zero-strict-low represented state the raw Hessian clock is
already zero.  Hence the represented state has an exact-active Hessian chart
independently of which branch of the C/D source-rank-three analysis was used,
and every such chart has a nonzero constant 3x3 Hessian minor.

Consequently the evaluated source-point constructor does not create a second
terminal obligation: both E3 constructors may be routed through the same
exact-active constant-minor resolver. -/
structure TopKernelLinearPowerE3ConstantFinalResolutionExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- The single constant-minor resolver supplies the older two-field E3
interface.  In the source-point branch we deliberately do not reconstruct a
second active chart from the evaluated 3x3 minor: raw defect zero already
provides an honest exact-active chart on this same represented source. -/
noncomputable def
    TopKernelLinearPowerE3ConstantFinalResolutionExtractor.toE3Extractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    P.TopKernelLinearPowerE3FinalResolutionExtractor where
  sourcePoint := by
    intro _Q
    rcases
        T.terminal.blocker.presented.zeroDefect_exactActiveFourBlock
          T.presented_zero with
      ⟨A⟩
    rcases P.exactActive_threeByThree_of_presentedZero A with ⟨Q⟩
    exact X.sourceConstant A Q
  sourceConstant := by
    intro A Q
    exact X.sourceConstant A Q

/-- Every linear-power top-kernel packet is therefore reduced to one genuine
polynomial-level extraction obligation: resolve one exact-active constant
3x3 source-minor event. -/
theorem exists_finalResolution_of_e3ConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  P.exists_finalResolution_of_e3Extractor (X.toE3Extractor P)

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
