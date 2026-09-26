import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRelativeSourceRankThree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureLongitudinalFirstContact
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

/-- **Marked-aware E3 frontier.**

Unlike the older source-rank-three compression, this interface consumes the
pure-longitudinal marked-axis constructor *before* entering the generic C/D
fallback.  That branch now retains either an honest balance-free first-contact
cross-facet carrier or a literal codimension-two source exponent.  All other
E2 constructors retain the terminal-aware C/D timing frontier. -/
inductive TopKernelLinearPowerE3MarkedAwareFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | pureFirstContact
      (data : P.PureLongitudinalBalanceFreeFirstContactData)
  | pureCodimensionTwoSource
      (d : Fin 4 →₀ ℕ)
      (mem_source : d ∈ T.representedSpecialFiber.support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (boundary : MvExponentOnCodimensionTwoBoundary d)
  | sourcePointThreeByThree
      (geometry : P.PositiveTailRepresentedSourceThreeByThreePointGeometry)
  | sourceConstantThreeByThree
      (active :
        AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented)
      (geometry :
        AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry active)
  | exactClosing
      (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer)
      (relative_pos : 0 < tail.relativeOrder)
      (binary : P.PositiveTailExplicitBinaryClockData clock)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (geometry : P.PositiveTailRankOneClosingSourcePointGeometry rankOne)

/-- The terminal-aware C/D frontier embeds into the marked-aware E3 frontier
without losing its exact-closing timing. -/
theorem TopKernelLinearPowerE3TerminalAwareFrontier.toMarkedAware
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (G : P.TopKernelLinearPowerE3TerminalAwareFrontier) :
    Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
  cases G with
  | sourcePointThreeByThree Q =>
      exact ⟨.sourcePointThreeByThree Q⟩
  | sourceConstantThreeByThree A Q =>
      exact ⟨.sourceConstantThreeByThree A Q⟩
  | exactClosing layer clock tangent tail hpos binary rankOne geometry =>
      exact ⟨.exactClosing layer clock tangent tail hpos binary rankOne geometry⟩

/-- **E2 -> marked-aware E3 refinement.**

The pure-longitudinal marked-axis branch is now removed from the generic
source-3x3 collapse.  Every other E2 constructor continues through the
terminal-aware C/D classifier. -/
theorem topKernelLinearPowerE3MarkedAwareFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
  have hfallback :
      ∀ E : P.TopKernelLinearPowerE2Frontier,
        Nonempty P.TopKernelLinearPowerE3MarkedAwareFrontier := by
    intro E
    rcases E.toE3TerminalAwareFrontier with ⟨G⟩
    exact G.toMarkedAware P

  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  cases E with
  | pureLongitudinal coefficient hcoeff hface hk cd =>
      rcases P.pureLongitudinalFirstContactFrontier_nonempty
          hcoeff hface with ⟨Q⟩
      rcases Q.toContactOrCodimensionTwoSource P with ⟨R⟩
      cases R with
      | firstContact data =>
          exact ⟨.pureFirstContact data⟩
      | codimensionTwoSource d hd hdeg hboundary =>
          exact ⟨.pureCodimensionTwoSource d hd hdeg hboundary⟩
  | fullFacetCodimensionTwo hfacet hboundary cd =>
      exact hfallback
        (.fullFacetCodimensionTwo hfacet hboundary cd)
  | fullFacetActualRankTwo hfacet geometry cd =>
      exact hfallback
        (.fullFacetActualRankTwo hfacet geometry cd)
  | crossFacetNear data hboundary cd =>
      exact hfallback
        (.crossFacetNear data hboundary cd)
  | crossFacetFar data hboundary cd =>
      exact hfallback
        (.crossFacetFar data hboundary cd)

/-- Canonical marked-aware E3 output. -/
noncomputable def topKernelLinearPowerE3MarkedAwareFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelLinearPowerE3MarkedAwareFrontier :=
  Classical.choice P.topKernelLinearPowerE3MarkedAwareFrontier_nonempty

/-- **Timing-preserving E3 final-resolution extractor.**

The source-point and source-constant branches are retained exactly as in the
older E3 interface.  Crucially, the positive-relative rank-one exact-closing
branch is *not* collapsed to generic represented-source rank-three geometry:
its exact clock, tangent tail, binary/rank-one packets and whole-family
first-opening geometry remain available to the final endpoint producer. -/
structure TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor
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
  exactClosing :
    ∀ (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer),
      0 < tail.relativeOrder →
      ∀ (binary : P.PositiveTailExplicitBinaryClockData clock)
        (rankOne : P.PositiveTailExplicitRankOneClockData binary),
        P.PositiveTailRankOneClosingSourcePointGeometry rankOne →
          Nonempty
            (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- The terminal-aware E3 frontier feeds the timing-preserving extractor
without discarding the exact-closing first-opening data. -/
theorem exists_finalResolution_of_e3TerminalAwareExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases P.topKernelLinearPowerE2Frontier_nonempty with ⟨E⟩
  rcases E.toE3TerminalAwareFrontier with ⟨G⟩
  cases G with
  | sourcePointThreeByThree Q =>
      exact X.sourcePoint Q
  | sourceConstantThreeByThree A Q =>
      exact X.sourceConstant A Q
  | exactClosing layer clock tangent tail hpos binary rankOne geometry =>
      exact X.exactClosing layer clock tangent tail hpos binary rankOne geometry

/-- At raw defect zero the evaluated source-point event can still be routed
through the canonical exact-active constant 3x3 chart.  Preserving exact
closing therefore leaves exactly *two* genuine endpoint obligations:
the constant source chart and the timing-rich exact-closing branch. -/
structure TopKernelLinearPowerE3TerminalAwareConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  sourceConstant :
    ∀ (A : AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented),
      AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry A →
        Nonempty
          (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
  exactClosing :
    ∀ (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (tail : ThreeSchurTangentTailKernelOpeningData clock layer),
      0 < tail.relativeOrder →
      ∀ (binary : P.PositiveTailExplicitBinaryClockData clock)
        (rankOne : P.PositiveTailExplicitRankOneClockData binary),
        P.PositiveTailRankOneClosingSourcePointGeometry rankOne →
          Nonempty
            (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

/-- Convert the two-obligation terminal-aware interface to the full
three-constructor timing-preserving extractor. -/
noncomputable def
    TopKernelLinearPowerE3TerminalAwareConstantExtractor.toTerminalAwareExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareConstantExtractor) :
    P.TopKernelLinearPowerE3TerminalAwareFinalResolutionExtractor where
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
  exactClosing := by
    intro layer clock tangent tail hpos binary rankOne geometry
    exact X.exactClosing layer clock tangent tail hpos binary rankOne geometry

/-- Timing-preserving assembly with the evaluated source-point constructor
already absorbed into the zero-defect exact-active chart. -/
theorem exists_finalResolution_of_e3TerminalAwareConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3TerminalAwareConstantExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  P.exists_finalResolution_of_e3TerminalAwareExtractor
    (X.toTerminalAwareExtractor P)

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

/-- Every linear-power top-kernel packet is therefore reduced to one genuine
polynomial-level extraction obligation if one deliberately forgets the
exact-closing timing.  The terminal-aware interface above is preferred for
new endpoint work. -/
theorem exists_finalResolution_of_e3ConstantExtractor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (X : P.TopKernelLinearPowerE3ConstantFinalResolutionExtractor) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) :=
  P.exists_finalResolution_of_e3Extractor (X.toE3Extractor P)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
