import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedZeroLinearJetKernelOpening
import Mathlib.Tactic

/-!
# A18.4.67: positive presented-blocker slope is directly rank two

A18.4.50 still retained an unramified same-scale alternative for a positive
saturated rational slope.  A18.4.65--66 show that this alternative is absent
for the actual signed right-recentered blocker family: its full source gradient
vanishes at the origin, so even a kernel-linear first-contact monomial creates
a nonzero mixed Hessian entry.

This file reruns the three-coordinate rational normalisation with that stronger
fact.  Every positive transverse slope now gives geometry-backed rank-two
progress from the original source; the only non-progress alternative is zero
saturated slope in all three transverse coordinates.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- A positive saturated slope on the honest right-recentered blocker family
produces complete first-contact rank-two geometry after the determinant-one
sign presentation. -/
theorem positiveRecenteredSaturatedKernelSlope_completeRankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily)
    (hq :
      0 < saturatedKernelSlope kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily hactive) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR source complexity) := by
  let signed := D.signedRightRecenteredState
  let hmove := D.signedRightRecenteredPresentation
  have hfree0 :
      ∀ d ∈
          (polynomialFamilySpecialFiber
            D.blocker.aligned.endpoint.rightRecenteredFamily).support,
        d kernel = 0 :=
    specialFiber_free_of_saturatedKernelSlope_pos
      (K := K) kernel D.blocker.aligned.endpoint.rightRecenteredFamily hactive hq
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber signed.family).support,
        d kernel = 0 := by
    simpa [signed] using D.signedRightRecentered_specialFiber_free kernel hfree0
  have hactiveSigned : IsActiveKernelCoordinate kernel signed.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel signed.family signed.rawDefect signed.hessianDefect
  have hsource : HasCertifiedRamifiedEpisodeInternalMove signed source :=
    D.sourcePresentation.trans ⟨hmove⟩
  have hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i signed.family) = 0 := by
    simpa [signed] using D.signedRightRecenteredState_gradientAtZero
  exact source.presentedKernelFree_rankTwoProgress_of_gradientAtZero
    RR signed complexity hsrepair hsource kernel hkernel hactiveSigned hfree hgrad

/-- One transverse rational slope is either zero or already complete
geometry-backed rank-two progress. -/
inductive CompleteKernelNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (kernel : Fin 4) : Prop
  | rankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | zeroSlope
      (Z : AdaptiveRecenteredKernelZeroRationalSlopeObstruction D.blocker kernel)

/-- Complete one-coordinate normalisation with no same-scale recursive output. -/
theorem completeKernelNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    CompleteKernelNormalizationOutcome RR D complexity kernel := by
  let hactive :
      IsActiveKernelCoordinate kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel D.blocker.aligned.endpoint.rightRecenteredFamily
      D.blocker.aligned.endpoint.defect
      D.blocker.aligned.endpoint.rightRecenteredFamily_hessianDefect
  let q := saturatedKernelSlope kernel
    D.blocker.aligned.endpoint.rightRecenteredFamily hactive
  by_cases hzero : q = 0
  · exact .zeroSlope ⟨hactive, by simpa [q, hactive] using hzero⟩
  · have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    exact .rankTwo
      (D.positiveRecenteredSaturatedKernelSlope_completeRankTwoProgress
        RR complexity hsrepair kernel hkernel hactive
        (by simpa [q, hactive] using hpos))

/-- Complete three-coordinate rational normalisation.  The old
`presentedSameScale` constructor has disappeared. -/
inductive CompleteRationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | rankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | stationary
      (Z : AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker)
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (blocker_eq : S.blocker = D.blocker)

/-- **A18.4.67 complete presented rational normalisation.** -/
theorem completeRationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    CompleteRationalNormalizationOutcome RR D complexity := by
  cases D.completeKernelNormalizationOutcome
      RR complexity hsrepair (1 : Fin 4) (by decide) with
  | rankTwo P =>
      exact .rankTwo P
  | zeroSlope h₁ =>
      cases D.completeKernelNormalizationOutcome
          RR complexity hsrepair (2 : Fin 4) (by decide) with
      | rankTwo P =>
          exact .rankTwo P
      | zeroSlope h₂ =>
          cases D.completeKernelNormalizationOutcome
              RR complexity hsrepair (3 : Fin 4) (by decide) with
          | rankTwo P =>
              exact .rankTwo P
          | zeroSlope h₃ =>
              let Z : AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker :=
                ⟨h₁, h₂, h₃⟩
              let S := D.toScaleSoundStationaryBlocker Z
              exact .stationary Z S rfl

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
