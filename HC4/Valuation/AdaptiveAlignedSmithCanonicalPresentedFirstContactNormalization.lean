import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedKernelFirstContact
import Mathlib.Tactic

/-!
# A18.4.50: presented rational normalisation with no ramified-spend output

A18.4.49 replaces a positive transverse saturated slope by first-contact
termination.  Running that replacement in coordinates `1,2,3` gives the
sound version of A18.4.33's rational normaliser.

The only outcomes are:

* same-scale strict progress from the already-presented state;
* geometry-backed rank-two progress from the original source; or
* zero saturated rational slope in all three transverse directions, supplying
  the existing stationary blocker interface.

In particular there is no `GlobalRamifiedStrictMacro` constructor here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- One-coordinate first-contact-aware rational normalisation. -/
inductive FirstContactKernelNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (kernel : Fin 4) : Prop
  | presentedSameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : CertifiedSameScaleEpisodeProgress RR target D.presented)
  | rankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankTwoProgress
          RR D complexity))
  | zeroSlope
      (Z : AdaptiveRecenteredKernelZeroRationalSlopeObstruction D.blocker kernel)

/-- A single transverse coordinate either exits by first-contact progress or
has saturated rational slope zero. -/
theorem firstContactKernelNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    FirstContactKernelNormalizationOutcome RR D complexity kernel := by
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
    rcases D.positiveRecenteredSaturatedKernelSlope_sameScale_or_rankTwoProgress
        RR complexity hsrepair kernel hkernel hactive
        (by simpa [q, hactive] using hpos) with hstrict | hRankTwo
    · rcases hstrict with ⟨target, ht⟩
      exact .presentedSameScale target ht
    · exact .rankTwo hRankTwo

/-- Complete first-contact-aware rational normalisation of a presented
blocker. -/
inductive FirstContactRationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | presentedSameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : CertifiedSameScaleEpisodeProgress RR target D.presented)
  | rankTwo
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankTwoProgress
          RR D complexity))
  | stationary
      (Z : AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker)
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (blocker_eq : S.blocker = D.blocker)

/-- **A18.4.50 presented first-contact normalisation.** -/
theorem firstContactRationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    FirstContactRationalNormalizationOutcome RR D complexity := by
  cases D.firstContactKernelNormalizationOutcome
      RR complexity hsrepair (1 : Fin 4) (by decide) with
  | presentedSameScale target h =>
      exact .presentedSameScale target h
  | rankTwo P =>
      exact .rankTwo P
  | zeroSlope h₁ =>
      cases D.firstContactKernelNormalizationOutcome
          RR complexity hsrepair (2 : Fin 4) (by decide) with
      | presentedSameScale target h =>
          exact .presentedSameScale target h
      | rankTwo P =>
          exact .rankTwo P
      | zeroSlope h₂ =>
          cases D.firstContactKernelNormalizationOutcome
              RR complexity hsrepair (3 : Fin 4) (by decide) with
          | presentedSameScale target h =>
              exact .presentedSameScale target h
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
