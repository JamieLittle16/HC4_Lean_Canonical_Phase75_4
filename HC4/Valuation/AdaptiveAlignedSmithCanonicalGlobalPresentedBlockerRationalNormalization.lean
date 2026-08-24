import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerGeometry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedProgressUpgrade
import Mathlib.Tactic

/-!
# A18.4.33: rational-kernel normalisation at the presented blocker scale

The late stationary closing theorems require saturated rational kernel slope
zero in all three transverse source coordinates.  The old global normaliser
establishes exactly that dichotomy, but packages a positive slope at the
historical `20 * source.scale` aligned clock.  A presented blocker is already
past that coordinate change, and primitive entries may live at scale one.

This file repeats only the absolute-scale packaging of the already-proved
rational-kernel construction.  For a positive slope on the honest
right-recentered family we use the same

  denominator clearing -> integral kernel blow-up -> recentering

geometry, but record the target at

  R * presented.scale.

Because the blocker endpoint clock is exactly `presented.rawDefect`, the
resulting clock

  R * presented.rawDefect - 2*q

is an honest ramified raw-defect spend from the presented state.  If no such
positive slope exists in coordinates 1, 2, or 3, the existing all-transverse
zero-rational-slope stationary hypothesis is recovered.

No additional aligned-Smith ramification or homogeneity assumption is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- A positive saturated rational slope of a presented blocker's honest
right-recentered family gives a genuine strict macro at its current absolute
scale. -/
theorem globalRamifiedStrictMacro_of_positiveRecenteredSaturatedKernelSlope
    (RR : RepairRanking)
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
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let s := D.presented
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

  have hdegree₀ : NonlinearDegreeBound s.degreeCap P₀ := by
    simpa [P₀, E, B, s] using E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R P₀ hdegree₀
  have hdegree₁ : NonlinearDegreeBound s.degreeCap P₁ := by
    dsimp [P₁]
    exact nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q kernel Pram hdegreeRam hdiv
  have hdegree₂ : NonlinearDegreeBound s.degreeCap P₂ := by
    dsimp [P₂]
    exact nonlinearDegreeBound_polynomialFamilyTranslationHom
      s.degreeCap r₁ P₁ hdegree₁

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

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * E.defect - 2 * q
      scale := R * s.scale
      scale_pos := Nat.mul_pos hRpos s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P₂
      movingSection := b₂
      hessianDefect := hdef₂
      nonlinearDegreeBound := hdegree₂
      exactCollision := hcoll₂
      sectionSpecial := hb₂special }

  have hraw : target.rawDefect < R * s.rawDefect := by
    calc
      target.rawDefect = R * E.defect - 2 * q := by rfl
      _ < R * E.defect := hclock
      _ = R * s.rawDefect := by
        rw [show E.defect = s.rawDefect by simpa [E, B, s] using D.defect_eq]

  have hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
    change Nonempty (CertifiedRamifiedRawDefectSpend target s)
    exact ⟨{
      ramification := R
      ramification_pos := hRpos
      scale_eq := by rfl
      raw_lt := hraw
    }⟩

  exact (hspend.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation

/-- One-coordinate current-scale rational normalisation. -/
theorem ramifiedStrictMacro_or_recenteredZeroRationalSlope
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source ∨
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
  · exact Or.inr ⟨hactive, by simpa [q, hactive] using hzero⟩
  · have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    exact Or.inl
      (D.globalRamifiedStrictMacro_of_positiveRecenteredSaturatedKernelSlope
        RR kernel hkernel hactive (by simpa [q, hactive] using hpos))

/-- Run current-scale rational normalisation in all three transverse
coordinates. -/
theorem ramifiedStrictMacro_or_allTransverseZeroRationalSlope
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source ∨
      AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker := by
  rcases D.ramifiedStrictMacro_or_recenteredZeroRationalSlope
      RR (1 : Fin 4) (by decide) with hstrict | h₁
  · exact Or.inl hstrict
  rcases D.ramifiedStrictMacro_or_recenteredZeroRationalSlope
      RR (2 : Fin 4) (by decide) with hstrict | h₂
  · exact Or.inl hstrict
  rcases D.ramifiedStrictMacro_or_recenteredZeroRationalSlope
      RR (3 : Fin 4) (by decide) with hstrict | h₃
  · exact Or.inl hstrict
  exact Or.inr ⟨h₁, h₂, h₃⟩

/-- The zero-rational-slope side canonically supplies the existing stationary
blocker interface.  Its historical `defect ≤ 20 * rawDefect` field is only a
bound; the stronger current-scale equality is retained separately by
`D.defect_eq`. -/
noncomputable def toScaleSoundStationaryBlocker
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (Z : AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker) :
    AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented := by
  rcases D.blocker.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
  have hR : 1 ≤ alignedSmithRamificationIndex :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt alignedSmithRamificationIndex_pos)
  have hbound :
      D.blocker.aligned.endpoint.defect ≤
        alignedSmithRamificationIndex * D.presented.rawDefect := by
    rw [D.defect_eq]
    simpa using Nat.mul_le_mul_right D.presented.rawDefect hR
  exact {
    provenance := {
      blocker := D.blocker
      defect_le := hbound
    }
    mixed := M
    mixed_eq := hM
    allTransverseZero := Z
  }

/-- Final A18.4.33 interface: either strict progress has already occurred, or
we have the exact stationary hypotheses needed by the existing deep closing
geometry, still on the presented blocker family. -/
inductive RationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) : Prop
  | strictMacro
      (P : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)
  | stationary
      (Z : AdaptiveRecenteredAllTransverseZeroRationalSlope D.blocker)
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (blocker_eq : S.blocker = D.blocker)

/-- **A18.4.33 presented blocker rational normalisation.** -/
theorem rationalNormalizationOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    RationalNormalizationOutcome RR D := by
  rcases D.ramifiedStrictMacro_or_allTransverseZeroRationalSlope RR with
    hstrict | hzero
  · exact .strictMacro hstrict
  · let S := D.toScaleSoundStationaryBlocker hzero
    exact .stationary hzero S rfl

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
