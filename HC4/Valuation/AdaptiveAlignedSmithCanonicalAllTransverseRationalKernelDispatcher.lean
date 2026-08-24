import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroSchurRationalKernelDispatcher
import Mathlib.Tactic

/-!
# All-transverse saturated rational-kernel normalisation

The zero-Schur rational-kernel dispatcher resolves every positive saturated
coordinate-`3` slope on the exposed zero-Schur source.  The construction used
there is actually independent of the zero-Schur clock: after right recentering,
any non-longitudinal source coordinate may be denominator-cleared, blown up,
and recentered once more.  A positive saturated slope therefore gives strict
fixed-scale progress for an arbitrary adaptive blocker.

This file extracts that geometry in its correct general form and applies it to
all three transverse source coordinates `1`, `2`, and `3`.  Thus every residual
blocker branch of the current canonical dispatcher is normalised as follows:

* a positive saturated rational slope in any transverse coordinate is certified
  strict progress;
* otherwise the right-recentered family has saturated slope exactly zero in
  every transverse coordinate.  In particular each transverse coordinate is
  represented by an actual monomial of the recentered special fibre.

No homogeneity, terminal extraction, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Exact zero saturated rational slope on one source coordinate of the honest
right-recentered blocker family. -/
structure AdaptiveRecenteredKernelZeroRationalSlopeObstruction
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (kernel : Fin 4) : Prop where
  active :
    IsActiveKernelCoordinate kernel
      B.aligned.endpoint.rightRecenteredFamily
  saturated_eq_zero :
    saturatedKernelSlope kernel
        B.aligned.endpoint.rightRecenteredFamily active = 0

namespace AdaptiveRecenteredKernelZeroRationalSlopeObstruction

/-- Zero saturated rational slope is witnessed at parameter order zero: some
special-fibre monomial really uses the indicated source coordinate. -/
theorem specialFiber_witness
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    {kernel : Fin 4}
    (Z : AdaptiveRecenteredKernelZeroRationalSlopeObstruction B kernel) :
    ∃ d ∈
        (polynomialFamilySpecialFiber
          B.aligned.endpoint.rightRecenteredFamily).support,
      0 < d kernel := by
  by_contra hW
  have hfree :
      ∀ d ∈
          (polynomialFamilySpecialFiber
            B.aligned.endpoint.rightRecenteredFamily).support,
        d kernel = 0 := by
    intro d hd
    by_contra hne
    apply hW
    exact ⟨d, hd, Nat.pos_of_ne_zero hne⟩
  have hpos :
      0 < saturatedKernelSlope kernel
        B.aligned.endpoint.rightRecenteredFamily Z.active :=
    saturatedKernelSlope_pos
      kernel B.aligned.endpoint.rightRecenteredFamily Z.active hfree
  exact (Nat.ne_of_gt hpos) Z.saturated_eq_zero

end AdaptiveRecenteredKernelZeroRationalSlopeObstruction

namespace AdaptiveAlignedSmithBlockerEndpoint

/-- A positive saturated rational slope on any non-longitudinal coordinate of
an honest right-recentered blocker is strict adaptive progress after
ramification, integral kernel blow-up, and the canonical second recentering. -/
theorem exists_certifiedFixedScaleStrictSuccessor_of_positiveRecenteredSaturatedKernelSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive :
      IsActiveKernelCoordinate kernel
        B.aligned.endpoint.rightRecenteredFamily)
    (hq :
      0 < saturatedKernelSlope kernel
        B.aligned.endpoint.rightRecenteredFamily hactive) :
    ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target source := by
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
    simpa [q, P₀] using hq

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
    simpa [P₀, E] using E.rightRecenteredFamily_nonlinearDegreeBound
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
    simpa [P₀, r₀, E] using E.rightRecenteredFamily_exactCollision
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
    simpa [r₀, E] using E.rightRecenteredRightSection_specialPoint
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

/-- Universal saturated-rational normalisation on one non-longitudinal source
coordinate. -/
theorem certifiedStrict_or_recenteredZeroRationalSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    (∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target source) ∨
      AdaptiveRecenteredKernelZeroRationalSlopeObstruction B kernel := by
  let hactive :
      IsActiveKernelCoordinate kernel
        B.aligned.endpoint.rightRecenteredFamily :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel B.aligned.endpoint.rightRecenteredFamily
      B.aligned.endpoint.defect
      B.aligned.endpoint.rightRecenteredFamily_hessianDefect
  let q := saturatedKernelSlope kernel
    B.aligned.endpoint.rightRecenteredFamily hactive
  by_cases hzero : q = 0
  · right
    refine ⟨hactive, ?_⟩
    simpa [q, hactive] using hzero
  · left
    have hpos : 0 < q := Nat.pos_of_ne_zero hzero
    apply B.exists_certifiedFixedScaleStrictSuccessor_of_positiveRecenteredSaturatedKernelSlope
      RR s kernel hkernel hactive
    simpa [q, hactive] using hpos

end AdaptiveAlignedSmithBlockerEndpoint

/-- The final common source normal form after saturated-rational kernel
normalisation in all three transverse directions. -/
structure AdaptiveRecenteredAllTransverseZeroRationalSlope
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop where
  first :
    AdaptiveRecenteredKernelZeroRationalSlopeObstruction B (1 : Fin 4)
  second :
    AdaptiveRecenteredKernelZeroRationalSlopeObstruction B (2 : Fin 4)
  third :
    AdaptiveRecenteredKernelZeroRationalSlopeObstruction B (3 : Fin 4)

namespace AdaptiveRecenteredAllTransverseZeroRationalSlope

/-- Every transverse source coordinate occurs in the right-recentered special
fibre of the all-zero-rational-slope normal form. -/
theorem specialFiber_witnesses
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (Z : AdaptiveRecenteredAllTransverseZeroRationalSlope B) :
    (∃ d ∈
        (polynomialFamilySpecialFiber
          B.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (1 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          B.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (2 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          B.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (3 : Fin 4)) := by
  exact ⟨Z.first.specialFiber_witness,
    Z.second.specialFiber_witness,
    Z.third.specialFiber_witness⟩

end AdaptiveRecenteredAllTransverseZeroRationalSlope

namespace AdaptiveAlignedSmithBlockerEndpoint

/-- Run the generic rational-kernel normalisation successively in all three
transverse directions. -/
theorem certifiedStrict_or_allTransverseZeroRationalSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap) :
    (∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target source) ∨
      AdaptiveRecenteredAllTransverseZeroRationalSlope B := by
  rcases B.certifiedStrict_or_recenteredZeroRationalSlope
      RR s (1 : Fin 4) (by decide) with hstrict | h₁
  · exact Or.inl hstrict
  rcases B.certifiedStrict_or_recenteredZeroRationalSlope
      RR s (2 : Fin 4) (by decide) with hstrict | h₂
  · exact Or.inl hstrict
  rcases B.certifiedStrict_or_recenteredZeroRationalSlope
      RR s (3 : Fin 4) (by decide) with hstrict | h₃
  · exact Or.inl hstrict
  exact Or.inr ⟨h₁, h₂, h₃⟩

end AdaptiveAlignedSmithBlockerEndpoint

/-! ## Global dispatcher in the all-transverse rational normal form -/

inductive AdaptiveAlignedSmithCanonicalAllTransverseRationalKernelOutcome
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

  | blockerSchurEarlyActualLayerAllTransverseZeroRational
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (hlt : C.firstActualLayerOrder < B.aligned.endpoint.defect)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)
      (ZA : AdaptiveRecenteredAllTransverseZeroRationalSlope B)

  | blockerSchurEarlierWallAllTransverseZeroRational
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (hwall : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWall D)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)
      (ZA : AdaptiveRecenteredAllTransverseZeroRationalSlope B)

  | blockerZeroSchurAllTransverseZeroRational
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
      (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
      (W : AdaptiveAlignedSmithZeroSchurZeroRationalSlopeWitness C)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)
      (ZA : AdaptiveRecenteredAllTransverseZeroRationalSlope B)

  | blockerPlanarRigidPacketAllTransverseZeroRational
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)
      (ZA : AdaptiveRecenteredAllTransverseZeroRationalSlope B)

  | blockerWSquareRigidPacketAllTransverseZeroRational
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)
      (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
        B adaptiveCanonicalCommonKernel)
      (ZA : AdaptiveRecenteredAllTransverseZeroRationalSlope B)

/-- **All-transverse rational-kernel dispatcher.**

Every positive saturated rational slope in every transverse source direction
has now been consumed as certified strict episode progress. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalAllTransverseRationalKernelDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalAllTransverseRationalKernelOutcome
      RR s complexity := by
  rcases
      s.alignedSmithCanonicalZeroSchurRationalKernelDispatcher
        RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt, Z, ZR⟩ |
    ⟨B, C, D, hwall, Z, ZR⟩ |
    ⟨B, C, O, W, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · rcases B.certifiedStrict_or_allTransverseZeroRationalSlope RR s with
      hprogress | ZA
    · exact .strict hprogress
    · exact .blockerSchurEarlyActualLayerAllTransverseZeroRational
        B C hlt Z ZR ZA

  · rcases B.certifiedStrict_or_allTransverseZeroRationalSlope RR s with
      hprogress | ZA
    · exact .strict hprogress
    · exact .blockerSchurEarlierWallAllTransverseZeroRational
        B C D hwall Z ZR ZA

  · rcases B.certifiedStrict_or_allTransverseZeroRationalSlope RR s with
      hprogress | ZA
    · exact .strict hprogress
    · exact .blockerZeroSchurAllTransverseZeroRational B C O W Z ZR ZA

  · rcases B.certifiedStrict_or_allTransverseZeroRationalSlope RR s with
      hprogress | ZA
    · exact .strict hprogress
    · exact .blockerPlanarRigidPacketAllTransverseZeroRational
        B hall P hrigid Z ZR ZA

  · rcases B.certifiedStrict_or_allTransverseZeroRationalSlope RR s with
      hprogress | ZA
    · exact .strict hprogress
    · exact .blockerWSquareRigidPacketAllTransverseZeroRational
        B hall P hrigid Z ZR ZA

end

end HC4.Valuation
