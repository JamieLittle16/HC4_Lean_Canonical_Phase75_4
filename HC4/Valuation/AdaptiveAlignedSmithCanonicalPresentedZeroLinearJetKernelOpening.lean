import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroLinearJetKernelOpening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerFirstContactClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingKernelFirstContact
import HC4.Valuation.AdaptiveAlignedSmithExposureGeometry
import Mathlib.Tactic

/-!
# A18.4.66: zero-linear-jet first contact through arbitrary presentations

A18.4.65 closes a kernel-free first contact directly by geometry whenever the
presented family has zero source gradient at its literal origin.  The actual
A18 aligned proof reaches such families after several honest pure
presentations: aligned Smith exposure, right recentering followed by a sign
change, and determinant-one transverse source shears.

The finite rank promotion is insensitive to those presentation scales because
its recursive comparison uses the genuine rank-one -> rank-two repair
coordinate only.  This file records that composition once, and exports the
small zero-gradient preservation lemmas needed by the concrete blocker and
surviving adapters.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Simultaneous source sign change preserves vanishing of the complete source
gradient at the literal source origin. -/
theorem gradientAtZero_allSourceSignHom
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i P) = 0) :
    ∀ i : Fin 4,
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i
            (allSourceSignHom (R := Polynomial K) P)) = 0 := by
  intro i
  rw [pderiv_allSourceSignHom]
  simp only [map_neg]
  have heval :
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (allSourceSignHom (R := Polynomial K) (MvPolynomial.pderiv i P)) =
        MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i P) := by
    simpa using
      (eval_allSourceSignHom_neg
        (R := Polynomial K)
        (fun _ : Fin 4 => (0 : Polynomial K))
        (MvPolynomial.pderiv i P))
  rw [heval, hgrad i]
  simp

/-- Adaptive surviving-wall exposure introduces no source monomial outside the
zero-jet-normalized input support, hence the exposed family still has a full
zero source jet. -/
theorem AdaptiveSurvivingWallExposureData.zeroSourceJet
    {a : AdaptiveGeometricRestartState (K := K)}
    {wall : IntegralAdaptiveSurvivingSmithWall a.normalizedSpecialFiber}
    (d : AdaptiveSurvivingWallExposureData a wall) :
    HasZeroSourceJet d.family := by
  let P := zeroJetNormalizedFamily a.family
  have hP : HasZeroSourceJet P := by
    simpa [P] using zeroJetNormalizedFamily_hasZeroSourceJet a.family
  apply hP.of_support_subset
  simpa [AdaptiveSurvivingWallExposureData.family, P] using
    support_adaptiveSmithExposureFamily_subset
      d.ramification.R wall.realization.combinedSourceWeight
      d.commonLevel P d.integrality

/-- Generic geometry-backed rank-two promotion reached after an arbitrary pure
presentation of the original rank-one source. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented source
  localProgress :
    AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
      RR presented complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress localProgress.target source

/-- Any complete first-contact rank promotion remains globally strict from an
older pure-presentation source, because the actual geometric target has rank
two while the original source is genuinely rank one. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
    (RR : RepairRanking)
    {source presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (P : AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
      RR presented complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
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
    localProgress := P
    globalProgress := hglobal
  }

/-- **Presented zero-gradient kernel-free first contact is direct global
rank-two progress.**

The presentation itself is never a recursive edge.  It is retained only as
provenance; A18.4.65 acts on the actual presented family and the finite repair
coordinate makes the resulting geometry-backed rank promotion globally strict
from the original source. -/
theorem ScaleAwareAdaptiveGeometricRestartState.presentedKernelFree_rankTwoProgress_of_gradientAtZero
    (RR : RepairRanking)
    (source presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented source)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel presented.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber presented.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i presented.family) = 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR source complexity) := by
  have hpresentedRepair : presented.repair = rankOneRepairState complexity := by
    rcases hsource with ⟨hmove⟩
    rw [hmove.repair_eq]
    exact hsrepair
  rcases presented.kernelFreeOpening_rankTwoProgress_of_gradientAtZero
      RR complexity hpresentedRepair kernel hkernel hactive hfree hgrad with ⟨P⟩
  exact ⟨
    AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.ofLocal
      RR complexity hsrepair hsource P
  ⟩

/-- The signed honest right-recentered blocker family has zero source gradient
at its origin.  This packages the exact-collision argument already proved for
the unsiged right-recentered family with the generic sign-preservation lemma
above. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.signedRightRecenteredState_gradientAtZero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    ∀ i : Fin 4,
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i D.signedRightRecenteredState.family) = 0 := by
  have hbase :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i
              D.blocker.aligned.endpoint.rightRecenteredFamily) = 0 :=
    D.blocker.rightRecenteredFamily_gradientAtZero
  have hsign := gradientAtZero_allSourceSignHom
    D.blocker.aligned.endpoint.rightRecenteredFamily hbase
  simpa [AdaptiveAlignedSmithCanonicalPresentedBlocker.signedRightRecenteredState]
    using hsign

end

end HC4.Valuation
