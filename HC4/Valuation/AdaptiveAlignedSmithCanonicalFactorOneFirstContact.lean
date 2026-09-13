import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningRankTwoProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockDispatcher
import Mathlib.Tactic

/-!
# A18.4.46: absorb factor-one presentations before first-contact recursion

A18.4.34 straightens a literal transverse constant Hessian kernel by source
transvections and a source sign change.  At the scale-aware level this is a
`CertifiedRamifiedEpisodeInternalMove` whose ramification factor is exactly
one.  Such a move is not merely scale-equivalent: it preserves the complete
fixed-scale episode key literally.

This file records that bridge once.  It then composes A18.4.45 through an
arbitrary factor-one presentation.  Consequently a kernel-free coordinate on
the presented family produces either

* certified same-scale progress from the original source; or
* a geometry-backed rank-two promotion on the actual saturated-opening family,
  globally strict from the original source by the finite repair measure.

No cross-scale rational order is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A certified ramified internal move with factor `1` is exactly a fixed-scale
internal move for every repair ranking. -/
theorem CertifiedRamifiedEpisodeInternalMove.toFixedScale_of_ramification_eq_one
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : CertifiedRamifiedEpisodeInternalMove presented source)
    (hfactor : hmove.ramification = 1) :
    FixedScaleEpisodeInternalMove RR.rank presented source := by
  constructor
  · unfold SameEpisodeScale
    calc
      presented.scale = hmove.ramification * source.scale := hmove.scale_eq
      _ = source.scale := by simp [hfactor]
  · unfold ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey
    have hraw : presented.rawDefect = source.rawDefect := by
      calc
        presented.rawDefect = hmove.ramification * source.rawDefect := hmove.raw_eq
        _ = source.rawDefect := by simp [hfactor]
    rw [hraw, hmove.repair_eq, hmove.sourceComplexity_eq]

/-- Propositional factor-one presentations can likewise be consumed by the
fixed-scale macro interface. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.toFixedScale_of_factor_one
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (hfactor :
      ∀ h : CertifiedRamifiedEpisodeInternalMove presented source,
        h.ramification = 1) :
    FixedScaleEpisodeInternalMove RR.rank presented source := by
  rcases hmove with ⟨h⟩
  exact h.toFixedScale_of_ramification_eq_one RR (hfactor h)

/-- Rank-two first-contact progress after a factor-one presentation, retaining
both the presentation and the actual opening geometry. -/
structure AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  presentation : CertifiedRamifiedEpisodeInternalMove presented source
  factor_one : presentation.ramification = 1
  openingProgress :
    AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
      RR presented complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      openingProgress.target source

/-- A geometry-backed rank-two opening after a factor-one presentation is also
globally strict from the pre-presentation source. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress.ofPresented
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hmove : CertifiedRamifiedEpisodeInternalMove presented source)
    (hfactor : hmove.ramification = 1)
    (D : AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
      RR presented complexity) :
    AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
      RR source complexity := by
  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress D.target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [D.target_eq]
    change RepairState.measure (rankTwoRepairState complexity) <
      RepairState.measure source.repair
    rw [hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    presented := presented
    presentation := hmove
    factor_one := hfactor
    openingProgress := D
    globalProgress := hglobal
  }

/-- **First contact through a factor-one presentation.**

The presented family may differ geometrically from the source, but because the
presentation has factor one its fixed-scale key is identical.  Thus the
unramified branch composes back to the source.  In the nonlinear branch the
actual opening family and Hessian witness are retained and the finite rank
promotion is strict from the source. -/
theorem ScaleAwareAdaptiveGeometricRestartState.factorOneKernelFreePresentation_sameScale_or_rankTwoProgress
    (RR : RepairRanking)
    (source presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hmove : CertifiedRamifiedEpisodeInternalMove presented source)
    (hfactor : hmove.ramification = 1)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel presented.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber presented.family).support,
        d kernel = 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target source) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
          RR source complexity) := by
  have hpresentedRepair : presented.repair = rankOneRepairState complexity := by
    rw [hmove.repair_eq]
    exact hsrepair
  rcases presented.kernelFreeOpening_sameScale_or_rankTwoProgress
      RR complexity hpresentedRepair kernel hkernel hactive hfree with
    hstrict | hRankTwo
  · rcases hstrict with ⟨target, ht⟩
    left
    refine ⟨target, ?_⟩
    exact
      (hmove.toFixedScale_of_ramification_eq_one RR hfactor).then_certifiedSameScaleProgress
        RR ht
  · rcases hRankTwo with ⟨D⟩
    right
    exact ⟨
      AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress.ofPresented
        RR complexity hsrepair hmove hfactor D
    ⟩

end

end HC4.Valuation
