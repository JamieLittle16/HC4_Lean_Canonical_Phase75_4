import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedEndpointScaleBridge
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedProgressUpgrade
import Mathlib.Tactic

/-!
# A18.4.32: normalize a presented blocker at its current absolute scale

A18.4.29--30 identify a boundary-produced canonical blocker with an actual
scale-aware state at the scale where the blocker really lives.  The historical
scale-sound rational-kernel dispatcher was written one level earlier, before
that presentation, and therefore measures its exits against a fresh aligned
factor `20`.  Reusing it here would ramify the bookkeeping scale a second time.

This file reruns only the already-proved saturated rational-kernel construction
with the presented endpoint as its source.  The polynomial operations are
unchanged:

* right recenter the canonical blocker;
* denominator-clear one saturated rational kernel slope;
* perform the integral kernel blow-up;
* recenter the marked pair back to the canonical axis.

If the slope is positive, the resulting target is recorded at scale
`R * presented.scale` and is an honest `CertifiedRamifiedRawDefectSpend` from
`presented` itself.  If all three transverse slopes are zero, we retain the
existing stationary blocker package together with the stronger current-scale
clock identity

    blocker.defect = presented.rawDefect.

No second aligned-Smith ramification, global homogeneity, or repair-only
successor is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- A positive saturated rational slope on the honest right-recentered family
of an already-presented blocker is a genuine ramified raw-defect spend from
that presented state at its *current* absolute scale. -/
theorem exists_certifiedRamifiedRawDefectSpend_of_positiveRecenteredSaturatedKernelSlope
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily)
    (hq :
      0 < saturatedKernelSlope kernel
        D.blocker.aligned.endpoint.rightRecenteredFamily hactive) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target D.presented := by
  let B := D.blocker
  let E := B.aligned.endpoint
  let P₀ := E.rightRecenteredFamily
  let r₀ := E.rightRecenteredRightSection
  let R := kernelSlopeDenominatorClearingRamification kernel P₀
  let q := saturatedKernelSlope kernel P₀ hactive
  let Pram := parameterRamificationFamily (K := K) R P₀
  let rram := parameterRamificationSection (K := K) R r₀
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel P₀ hactive
  let P₁ := integralKernelBlowupFamily kernel q Pram hdiv
  let r₁ := kernelBlowupSection kernel q rram
  let P₂ := polynomialFamilyTranslationHom (K := K) r₁ P₁
  let b₂ := polynomialSectionDifference r₁ (zeroPolynomialSection (K := K))

  have hRpos : 0 < R := by
    dsimp [R, P₀]
    exact kernelSlopeDenominatorClearingRamification_pos
      kernel E.rightRecenteredFamily
  have hqpos : 0 < q := by
    simpa [q, P₀, B, E] using hq

  have hdef₀ :
      HasPolynomialFamilyHessianDefect (K := K) P₀ E.defect := by
    simpa [P₀] using E.rightRecenteredFamily_hessianDefect
  have hdefRam :
      HasPolynomialFamilyHessianDefect (K := K) Pram (R * E.defect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R E.defect P₀ hdef₀
  have hdef₁ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₁ (R * E.defect - 2 * q) := by
    dsimp [P₁]
    exact integralKernelBlowup_hasHessianDefect_sub
      kernel q (R * E.defect) Pram hdiv hdefRam
  have hdef₂ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₂ (R * E.defect - 2 * q) := by
    dsimp [P₂]
    exact polynomialFamilyTranslationHom_preservesHessianDefect
      (K := K) r₁ P₁ hdef₁

  have hdegree₀ : NonlinearDegreeBound D.presented.degreeCap P₀ := by
    simpa [P₀, E, B] using E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegreeRam : NonlinearDegreeBound D.presented.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      D.presented.degreeCap R P₀ hdegree₀
  have hdegree₁ : NonlinearDegreeBound D.presented.degreeCap P₁ := by
    dsimp [P₁]
    exact nonlinearDegreeBound_integralKernelBlowup
      D.presented.degreeCap q kernel Pram hdegreeRam hdiv
  have hdegree₂ : NonlinearDegreeBound D.presented.degreeCap P₂ := by
    dsimp [P₂]
    exact nonlinearDegreeBound_polynomialFamilyTranslationHom
      D.presented.degreeCap r₁ P₁ hdegree₁

  have hcoll₀ :
      HasPolynomialFamilyExactGradientCollision
        P₀ (zeroPolynomialSection (K := K)) r₀ := by
    simpa [P₀, r₀, E, B] using E.rightRecenteredFamily_exactCollision
  have hcollRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)))
        rram := by
    dsimp [Pram, rram]
    exact polynomialFamilyExactGradientCollision_parameterRamification
      R P₀ (zeroPolynomialSection (K := K)) r₀ hcoll₀
  have hcoll₁raw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q Pram hdiv
      (parameterRamificationSection (K := K) R
        (zeroPolynomialSection (K := K)))
      rram hcollRam
  have hramZero :
      parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [parameterRamificationSection, zeroPolynomialSection]
  have hzeroSection :
      kernelBlowupSection kernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    rw [hramZero]
    exact kernelBlowupSection_zeroPolynomialSection kernel q
  have hcoll₁ :
      HasPolynomialFamilyExactGradientCollision
        P₁ (zeroPolynomialSection (K := K)) r₁ := by
    rw [hzeroSection] at hcoll₁raw
    simpa [P₁, r₁] using hcoll₁raw
  have hswap :
      HasPolynomialFamilyExactGradientCollision
        P₁ r₁ (zeroPolynomialSection (K := K)) := by
    intro i
    exact (hcoll₁ i).symm
  have hcoll₂ :
      HasPolynomialFamilyExactGradientCollision
        P₂ (zeroPolynomialSection (K := K)) b₂ := by
    simpa [P₂, b₂] using
      (polynomialFamilyExactGradientCollision_recenter
        (K := K) P₁ r₁ (zeroPolynomialSection (K := K)) hswap)

  have hrramSpecial :
      polynomialSectionSpecialPoint rram =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    dsimp [rram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos r₀]
    simpa [r₀, E, B] using E.rightRecenteredRightSection_specialPoint
  have hr₁special :
      polynomialSectionSpecialPoint r₁ =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hqpos rram]
      simp [coordinateAxisPoint, hkernel]
    · dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q rram hi]
      exact congrFun hrramSpecial i
  have hb₂special :
      polynomialSectionSpecialPoint b₂ =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [b₂]
    rw [polynomialSectionSpecialPoint_difference, hr₁special]
    funext i
    simp [zeroPolynomialSection, polynomialSectionSpecialPoint]

  have hcost : 2 * q ≤ R * E.defect := by
    exact two_mul_slope_le_of_integralKernelBlowup
      kernel q (R * E.defect) Pram hdiv hdefRam
  have hclock : R * E.defect - 2 * q < R * E.defect := by
    omega
  have hraw :
      R * E.defect - 2 * q < R * D.presented.rawDefect := by
    rw [← D.defect_eq]
    exact hclock

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * E.defect - 2 * q
      scale := R * D.presented.scale
      scale_pos := Nat.mul_pos hRpos D.presented.scale_pos
      degreeCap := D.presented.degreeCap
      sourceComplexity := D.presented.sourceComplexity
      repair := D.presented.repair
      family := P₂
      movingSection := b₂
      hessianDefect := hdef₂
      nonlinearDegreeBound := hdegree₂
      exactCollision := hcoll₂
      sectionSpecial := hb₂special }

  refine ⟨target, ?_⟩
  change Nonempty (CertifiedRamifiedRawDefectSpend target D.presented)
  exact ⟨{
    ramification := R
    ramification_pos := hRpos
    scale_eq := by rfl
    raw_lt := by simpa [target] using hraw
  }⟩

/-- Current-scale one-coordinate rational-kernel normalisation. -/
theorem ramifiedSpend_or_recenteredZeroRationalSlope
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target D.presented) ∨
      AdaptiveRecenteredKernelZeroRationalSlopeObstruction D.blocker kernel := by
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
  · right
    refine ⟨hactive, ?_⟩
    simpa [q, hactive] using hzero
  · left
    have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    apply D.exists_certifiedRamifiedRawDefectSpend_of_positiveRecenteredSaturatedKernelSlope
      kernel hkernel hactive
    simpa [q, hactive] using hpos

/-- Run the current-scale rational-kernel normalisation in all three transverse
coordinates. -/
theorem ramifiedSpend_or_allTransverseZeroRationalSlope
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target D.presented) ∨
      AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker := by
  rcases D.ramifiedSpend_or_recenteredZeroRationalSlope
      (1 : Fin 4) (by decide) with hstrict | h₁
  · exact Or.inl hstrict
  rcases D.ramifiedSpend_or_recenteredZeroRationalSlope
      (2 : Fin 4) (by decide) with hstrict | h₂
  · exact Or.inl hstrict
  rcases D.ramifiedSpend_or_recenteredZeroRationalSlope
      (3 : Fin 4) (by decide) with hstrict | h₃
  · exact Or.inl hstrict
  exact Or.inr ⟨h₁, h₂, h₃⟩

end AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- A boundary-produced blocker after rational-kernel normalisation, retaining
the stronger clock identity appropriate to its actual current scale. -/
structure AdaptiveAlignedSmithCanonicalPresentedStationaryBlocker
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  presentedBlocker : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source
  stationary :
    AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker
      presentedBlocker.presented
  blocker_eq : stationary.blocker = presentedBlocker.blocker
  current_clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      presentedBlocker.presented.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect

/-- Presented-blocker normalisation has no neutral output.  It either reflects
zero defect to the original source, exits by a genuine strict macro, or reaches
the all-transverse-zero stationary geometry while retaining the exact current
clock. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerNormalizationOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)
  | stationary
      (D : AdaptiveAlignedSmithCanonicalPresentedStationaryBlocker
        (K := K) source)

/-- **A18.4.32 current-scale presented-blocker normalisation.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.currentScaleNormalization
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerNormalizationOutcome
      RR source := by
  by_cases hzero : D.presented.rawDefect = 0
  · exact .zeroDefect
      (D.sourcePresentation.source_rawDefect_eq_zero_of_target hzero)

  rcases D.ramifiedSpend_or_allTransverseZeroRationalSlope with
    hspend | hstationary
  · rcases hspend with ⟨target, h⟩
    exact .ramifiedStrictMacro
      ((h.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation)
  · rcases D.blocker.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    let P : AdaptiveAlignedSmithBlockerClockProvenance (K := K) D.presented := {
      blocker := D.blocker
      defect_le := by
        rw [D.defect_eq]
        have hram := alignedSmithRamificationIndex_pos
        omega
    }
    let S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker
        (K := K) D.presented := {
      provenance := P
      mixed := M
      mixed_eq := by simpa [P] using hM
      allTransverseZero := hstationary
    }
    have hclock :
        S.blocker.aligned.endpoint.defect = D.presented.rawDefect := by
      simpa [S, P] using D.defect_eq
    have hpos : 0 < S.blocker.aligned.endpoint.defect := by
      rw [hclock]
      exact Nat.pos_of_ne_zero hzero
    exact .stationary {
      presentedBlocker := D
      stationary := S
      blocker_eq := by rfl
      current_clock_eq := hclock
      clock_pos := hpos
    }

end

end HC4.Valuation
