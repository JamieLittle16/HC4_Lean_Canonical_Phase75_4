import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedSurvivingClosure
import Mathlib.Tactic

/-!
# A18.4.52: surviving kernel-free exposure terminates by first contact

The only rational-recursive leaf in the presented surviving closure is the
kernel-free canonical Smith exposure.  The exposure itself is an honest pure
presentation of the current state.  Its special fibre is free of coordinate
`3`, so A18.4.45 applies directly on the actual exposed scale-aware state.

Consequently the exposure yields either a same-scale strict successor of that
exposed state or a nonlinear first-contact Hessian direction which licenses a
geometry-backed rank-one -> rank-two promotion on the actual saturated-opening
family.  The earlier source presentations are retained explicitly.

No cross-scale rational order is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A geometry-backed nonlinear first-contact promotion reached after an
arbitrary pure presentation of the original source. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedKernelExposureRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented source
  local : AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
    RR presented complexity
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    local.target source

/-- Finite repair promotion remains globally strict when prefixed by any pure
presentation, because the recursive comparison uses only the retained repair
coordinate. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedKernelExposureRankTwoProgress.ofLocal
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (P : AdaptiveAlignedSmithCanonicalGlobalKernelOpeningRankTwoProgress
      RR presented complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedKernelExposureRankTwoProgress
      RR source complexity := by
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress P.target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [P.target_eq]
    change RepairState.measure (rankTwoRepairState complexity) <
      RepairState.measure source.repair
    rw [hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    presented := presented
    sourcePresentation := hsource
    local := P
    globalProgress := hglobal
  }

/-- Sound first-contact outcome of a canonical kernel-free surviving exposure. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingKernelFirstContactOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | presentedSameScale
      (P : AdaptiveAlignedSmithCanonicalPresentedSameScaleProgress RR source)
  | rankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedKernelExposureRankTwoProgress
          RR source complexity))

/-- **Kernel-free surviving exposure first-contact theorem.**

The exposure state is the literal adaptive Smith exposure at its true absolute
scale.  Its special fibre is already known to omit coordinate `3`.  First
contact therefore closes the branch without exporting a ramified raw spend. -/
theorem AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint.firstContactOutcome_from_presented
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
      (K := K) D.presented)
    (hclock : E.W.original.aligned.endpoint.defect = D.presented.rawDefect)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalSurvivingKernelFirstContactOutcome
      RR source complexity := by
  let s := D.presented
  let a : AdaptiveGeometricRestartState (K := K) :=
    E.exposure.toAdaptiveState E.canonicalSpecial
  let exposed := a.toScaleAwareAt
    (E.exposure.ramification.R * s.scale)
    (Nat.mul_pos E.exposure.ramification.R_pos s.scale_pos)

  have hexposed : HasCertifiedRamifiedEpisodeInternalMove exposed s := by
    simpa [exposed, a, s] using
      E.exposure.certifiedInternalMove_from_presented
        E.W E.canonicalSpecial hclock

  have hsource : HasCertifiedRamifiedEpisodeInternalMove exposed source :=
    D.sourcePresentation.trans hexposed

  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber exposed.family).support,
        d (3 : Fin 4) = 0 := by
    simpa [exposed, a] using E.specialFiber_free_three

  have hactive : IsActiveKernelCoordinate (3 : Fin 4) exposed.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) exposed.family exposed.rawDefect exposed.hessianDefect

  have hexposedRepair : exposed.repair = rankOneRepairState complexity := by
    change s.repair = rankOneRepairState complexity
    rcases D.sourcePresentation with ⟨hmove⟩
    dsimp [s]
    rw [hmove.repair_eq]
    exact hsrepair

  rcases exposed.kernelFreeOpening_sameScale_or_rankTwoProgress
      RR complexity hexposedRepair (3 : Fin 4) (by decide) hactive hfree with
    hstrict | hRankTwo
  · rcases hstrict with ⟨target, ht⟩
    exact .presentedSameScale {
      presented := exposed
      sourcePresentation := hsource
      target := target
      progress := ht
    }
  · rcases hRankTwo with ⟨P⟩
    exact .rankTwo ⟨
      AdaptiveAlignedSmithCanonicalGlobalPresentedKernelExposureRankTwoProgress.ofLocal
        RR complexity hsrepair hsource P
    ⟩

end

end HC4.Valuation
