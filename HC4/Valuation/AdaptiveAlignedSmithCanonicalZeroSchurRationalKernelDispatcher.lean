import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroSchurOffenderDispatcher
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import Mathlib.Tactic

/-!
# Saturated rational-kernel resolution of the zero-Schur offender

The preceding dispatcher exposes a concrete source coefficient which reaches
coordinate `3` strictly before the integral zero-Schur candidate.  The honest
next object is therefore the saturated rational first kernel slope of the same
right-recentered family.

There is one important distinction.  Denominator clearing always makes that
slope integral, but the saturated slope need not be positive: it is zero
exactly when some active coordinate-`3` monomial already survives on the
special fibre.

This file resolves the positive case completely.  After denominator clearing
we perform the saturated integral kernel blow-up on the honest recentered
source, reverse the surviving exact collision, and recenter once more.  The
marked pair returns to `0 ~ e0`, nonlinear degree is preserved, and the
ramified raw Hessian defect drops by `2*q`.  Hence this is certified
fixed-scale progress.

If `q = 0`, the finite minimum which defines the saturated slope is attained.
The attaining active monomial must have exact parameter order zero, so it
really lies on the right-recentered special fibre with positive coordinate-3
degree.  Thus the residual zero-Schur branch is no longer a rational-wall
problem: it carries an explicit zero-order source witness.

No homogeneity, terminal extraction, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The precise residual obstruction after saturating the rational coordinate-3
kernel slope: an active coordinate-3 monomial is already present on the honest
right-recentered special fibre. -/
def AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) : Prop :=
  ∃ d ∈ (polynomialFamilySpecialFiber C.family).support,
    0 < d adaptiveCanonicalCommonKernel

namespace AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-- Every first-kernel offender is genuinely active in the common source
coordinate. -/
theorem firstKernelOffender_active
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C) :
    IsActiveKernelCoordinate adaptiveCanonicalCommonKernel C.family := by
  unfold AdaptiveAlignedSmithZeroSchurFirstKernelOffender at O
  rcases O with ⟨d, hd, hlt⟩
  refine ⟨d, hd, ?_⟩
  by_contra hnot
  have hd0 : d adaptiveCanonicalCommonKernel = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hd0] at hlt
  omega

/-- If the denominator-cleared saturated slope is zero, the honest
recentered special fibre cannot be free of the common kernel coordinate.
Thus an active coordinate-3 monomial already survives at parameter order
zero. -/
theorem zeroRationalSlopeWitness_of_saturatedKernelSlope_eq_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
    (hzero :
      saturatedKernelSlope adaptiveCanonicalCommonKernel C.family
          (C.firstKernelOffender_active O) = 0) :
    AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C := by
  unfold AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness
  let hactive := C.firstKernelOffender_active O
  by_contra hW
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber C.family).support,
        d adaptiveCanonicalCommonKernel = 0 := by
    intro d hd
    by_contra hne
    apply hW
    exact ⟨d, hd, Nat.pos_of_ne_zero hne⟩
  have hpos :
      0 < saturatedKernelSlope adaptiveCanonicalCommonKernel C.family hactive :=
    saturatedKernelSlope_pos
      adaptiveCanonicalCommonKernel C.family hactive hfree
  have hzero' :
      saturatedKernelSlope adaptiveCanonicalCommonKernel C.family hactive = 0 := by
    simpa [hactive] using hzero
  omega

/-- A positive saturated rational kernel slope is genuine strict adaptive
progress after denominator clearing.  The final recentering restores the
canonical marked pair `0 ~ e0`. -/
theorem exists_certifiedFixedScaleStrictSuccessor_of_positiveSaturatedKernelSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
    (hq :
      0 < saturatedKernelSlope adaptiveCanonicalCommonKernel C.family
        (C.firstKernelOffender_active O)) :
    ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target source := by
  let E := B.aligned.endpoint
  let P₀ := C.family
  let r₀ := E.rightRecenteredRightSection
  let hactive := C.firstKernelOffender_active O
  let R := kernelSlopeDenominatorClearingRamification
    adaptiveCanonicalCommonKernel P₀
  let q := saturatedKernelSlope adaptiveCanonicalCommonKernel P₀ hactive
  let Pram := parameterRamificationFamily (K := K) R P₀
  let rram := parameterRamificationSection (K := K) R r₀
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) adaptiveCanonicalCommonKernel P₀ hactive
  let P₁ := integralKernelBlowupFamily
    adaptiveCanonicalCommonKernel q Pram hdiv
  let r₁ := kernelBlowupSection adaptiveCanonicalCommonKernel q rram
  let P₂ := polynomialFamilyTranslationHom (K := K) r₁ P₁
  let b₂ := polynomialSectionDifference r₁ (zeroPolynomialSection (K := K))

  have hRpos : 0 < R := by
    dsimp [R, P₀]
    exact kernelSlopeDenominatorClearingRamification_pos
      adaptiveCanonicalCommonKernel C.family
  have hqpos : 0 < q := by
    simpa [q, P₀, hactive] using hq

  have hdef₀ :
      HasPolynomialFamilyHessianDefect (K := K) P₀ E.defect := by
    simpa [P₀] using C.family_hessianDefect
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
      adaptiveCanonicalCommonKernel q (R * E.defect) Pram hdiv hdefRam
  have hdef₂ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₂ (R * E.defect - 2 * q) := by
    dsimp [P₂]
    exact polynomialFamilyTranslationHom_preservesHessianDefect
      (K := K) r₁ P₁ hdef₁

  have hdegree₀ : NonlinearDegreeBound s.degreeCap P₀ := by
    simpa [P₀, E] using E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R P₀ hdegree₀
  have hdegree₁ : NonlinearDegreeBound s.degreeCap P₁ := by
    dsimp [P₁]
    exact nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q adaptiveCanonicalCommonKernel Pram hdegreeRam hdiv
  have hdegree₂ : NonlinearDegreeBound s.degreeCap P₂ := by
    dsimp [P₂]
    exact nonlinearDegreeBound_polynomialFamilyTranslationHom
      s.degreeCap r₁ P₁ hdegree₁

  have hcoll₀ :
      HasPolynomialFamilyExactGradientCollision
        P₀ (zeroPolynomialSection (K := K)) r₀ := by
    simpa [P₀, r₀, E] using C.family_exactCollision
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
      adaptiveCanonicalCommonKernel q Pram hdiv
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
      kernelBlowupSection adaptiveCanonicalCommonKernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    rw [hramZero]
    exact kernelBlowupSection_zeroPolynomialSection
      adaptiveCanonicalCommonKernel q
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
    simpa [r₀, E] using E.rightRecenteredRightSection_specialPoint
  have hr₁special :
      polynomialSectionSpecialPoint r₁ =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    funext i
    by_cases hi : i = adaptiveCanonicalCommonKernel
    · subst i
      dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        adaptiveCanonicalCommonKernel hqpos rram]
      simp [adaptiveCanonicalCommonKernel, coordinateAxisPoint]
    · dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        adaptiveCanonicalCommonKernel q rram hi]
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
      adaptiveCanonicalCommonKernel q (R * E.defect) Pram hdiv hdefRam
  have hclock : R * E.defect - 2 * q < R * E.defect := by
    omega

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := R * E.defect - 2 * q
      scale := R
      scale_pos := hRpos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P₂
      movingSection := b₂
      hessianDefect := hdef₂
      nonlinearDegreeBound := hdegree₂
      exactCollision := hcoll₂
      sectionSpecial := hb₂special }
  let a := B.aligned.toAdaptiveState s
  let source := a.parameterRamifiedScaleAwareState R hRpos

  refine ⟨source, target, ?_⟩
  apply certifiedFixedScaleEpisodeProgress_of_rawDefect_lt RR
  · rfl
  · change R * E.defect - 2 * q < R * E.defect
    exact hclock

/-- **Saturated rational-kernel dichotomy for the exposed zero-Schur
first-kernel offender.**

Every positive rational first kernel wall becomes certified strict progress
after denominator clearing.  The only surviving case is slope zero, witnessed
by an actual active monomial on the recentered special fibre. -/
theorem firstKernelOffender_strict_or_zeroRationalSlopeWitness
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C) :
    (∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target source) ∨
      AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C := by
  let hactive := C.firstKernelOffender_active O
  let q := saturatedKernelSlope adaptiveCanonicalCommonKernel C.family hactive
  by_cases hzero : q = 0
  · right
    apply C.zeroRationalSlopeWitness_of_saturatedKernelSlope_eq_zero O
    simpa [q, hactive] using hzero
  · left
    have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    apply C.exists_certifiedFixedScaleStrictSuccessor_of_positiveSaturatedKernelSlope
      RR s O
    simpa [q, hactive] using hpos

end AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-! ## Global dispatcher after positive rational kernel walls are consumed -/

/-- Canonical outcome after every positive saturated rational coordinate-3
kernel wall on the zero-Schur branch has been converted to strict progress.
The only surviving zero-Schur constructor carries a literal special-fibre
coordinate-3 monomial, i.e. saturated rational slope zero. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurRationalKernelOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  | blockerSchurEarlyActualLayerDoubleZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (hlt : C.firstActualLayerOrder < B.aligned.endpoint.defect)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)

  | blockerSchurEarlierWallDoubleZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (hwall : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWall D)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)

  | blockerZeroSchurZeroRationalSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
      (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
      (W : AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)

  | blockerPlanarRigidPacketDoubleZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket (0 : Fin 4) 1 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)

  | blockerWSquareRigidPacketDoubleZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket (0 : Fin 4) 3 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)

/-- Run the explicit-offender dispatcher and immediately consume every
positive saturated rational kernel wall on its zero-Schur branch. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalZeroSchurRationalKernelDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalZeroSchurRationalKernelOutcome
      RR s complexity := by
  rcases s.alignedSmithCanonicalZeroSchurOffenderDispatcher
      RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt, Z, ZR⟩ |
    ⟨B, C, D, hwall, Z, ZR⟩ |
    ⟨B, C, O, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact .blockerSchurEarlyActualLayerDoubleZeroSlope B C hlt Z ZR
  · exact .blockerSchurEarlierWallDoubleZeroSlope B C D hwall Z ZR
  · rcases C.firstKernelOffender_strict_or_zeroRationalSlopeWitness
      RR s O with hprogress | W
    · exact .strict hprogress
    · exact .blockerZeroSchurZeroRationalSlope B C O W Z ZR
  · exact .blockerPlanarRigidPacketDoubleZeroSlope B hall P hrigid Z ZR
  · exact .blockerWSquareRigidPacketDoubleZeroSlope B hall P hrigid Z ZR

end

end HC4.Valuation
