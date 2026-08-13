import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroSlopeDispatcher
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Canonical aligned-Smith dispatcher after recentered kernel normalisation

The first zero-slope dispatcher normalises the honest adaptive endpoint
family.  The remaining blocker geometry, however, is read on the honest
right-recentered source

    Q_tau(Y) = P_tau(Y + b(tau)),

whose marked collision is `0 ~ -b`.  Integral kernel divisibility is not
invariant in the reverse direction under this translation, so endpoint
zero-slope must not be silently reused as zero-slope for `Q`.

This file closes that presentation gap.

If the right-recentered family has a positive integral slope `q` in a
transverse coordinate, we

1. perform the honest integral kernel blow-up on `Q`;
2. retain its exact collision `0 ~ r`;
3. reverse that collision and recenter once more at `r`.

The second recentering changes the special marked pair from `0 ~ -e0` back
to the canonical `0 ~ e0`.  Source translation preserves both the pure
Hessian clock and the nonlinear degree ceiling, so the resulting family is
again an ordinary adaptive state.  Its exact defect is `Delta - 2*q`, hence
it is certified fixed-scale progress relative to the unrecentered adaptive
endpoint.

Consequently every residual blocker can now be normalised twice, once on the
endpoint presentation and once on the actual recentered presentation used by
the Schur/rigid geometry.  A surviving branch carries explicit zero-slope
certificates for both sources.

No homogeneity or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Degree control on the honest recentered source -/

/-- Affine right-recentering may create lower Taylor degrees, but it cannot
increase the nonlinear source-degree ceiling. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily_nonlinearDegreeBound
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    NonlinearDegreeBound degreeCap E.rightRecenteredFamily := by
  simpa [AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily] using
    nonlinearDegreeBound_polynomialFamilyTranslationHom
      degreeCap E.movingSection E.family E.nonlinearDegreeBound

/-! ## Positive recentered slope -> canonical adaptive strict successor -/

/-- Actual scale-one target obtained from a positive integral kernel slope on
the honest right-recentered blocker source.

After the kernel blow-up the marked pair is still `0 ~ -e0`.  Recentring at
the surviving right section, with the collision reversed, restores the
canonical adaptive presentation `0 ~ e0` without changing the new Hessian
clock. -/
noncomputable def AdaptiveAlignedSmithBlockerEndpoint.recenteredKernelScaleOneTarget
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (kernel : Fin 4)
    (q : ℕ)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility kernel q
        B.aligned.endpoint.rightRecenteredFamily)
    (hq : 0 < q)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let E := B.aligned.endpoint
  let P₀ := E.rightRecenteredFamily
  let r₀ := E.rightRecenteredRightSection
  let P₁ := integralKernelBlowupFamily kernel q P₀ hdiv
  let r₁ := kernelBlowupSection kernel q r₀
  let P₂ := polynomialFamilyTranslationHom (K := K) r₁ P₁
  let b₂ := polynomialSectionDifference r₁ (zeroPolynomialSection (K := K))

  have hdef₀ :
      HasPolynomialFamilyHessianDefect (K := K) P₀ E.defect := by
    simpa [P₀] using E.rightRecenteredFamily_hessianDefect

  have hdef₁ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₁ (E.defect - 2 * q) := by
    dsimp [P₁]
    exact
      integralKernelBlowup_hasHessianDefect_sub
        kernel q E.defect P₀ hdiv hdef₀

  have hdef₂ :
      HasPolynomialFamilyHessianDefect
        (K := K) P₂ (E.defect - 2 * q) := by
    dsimp [P₂]
    exact
      polynomialFamilyTranslationHom_preservesHessianDefect
        (K := K) r₁ P₁ hdef₁

  have hdegree₀ : NonlinearDegreeBound s.degreeCap P₀ := by
    simpa [P₀, E] using E.rightRecenteredFamily_nonlinearDegreeBound

  have hdegree₁ : NonlinearDegreeBound s.degreeCap P₁ := by
    dsimp [P₁]
    exact
      nonlinearDegreeBound_integralKernelBlowup
        s.degreeCap q kernel P₀ hdegree₀ hdiv

  have hdegree₂ : NonlinearDegreeBound s.degreeCap P₂ := by
    dsimp [P₂]
    exact
      nonlinearDegreeBound_polynomialFamilyTranslationHom
        s.degreeCap r₁ P₁ hdegree₁

  have hcoll₀ :
      HasPolynomialFamilyExactGradientCollision
        P₀ (zeroPolynomialSection (K := K)) r₀ := by
    simpa [P₀, r₀] using E.rightRecenteredFamily_exactCollision

  have hcoll₁raw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q P₀ hdiv
      (zeroPolynomialSection (K := K)) r₀ hcoll₀

  have hzero :
      kernelBlowupSection kernel q (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) :=
    kernelBlowupSection_zeroPolynomialSection kernel q

  have hcoll₁ :
      HasPolynomialFamilyExactGradientCollision
        P₁ (zeroPolynomialSection (K := K)) r₁ := by
    rw [hzero] at hcoll₁raw
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

  have hr₁special :
      polynomialSectionSpecialPoint r₁ =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hq r₀]
      simp [coordinateAxisPoint, hkernel]
    · dsimp [r₁]
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q r₀ hi]
      have hri := congrFun E.rightRecenteredRightSection_specialPoint i
      simpa [r₀] using hri

  have hb₂special :
      polynomialSectionSpecialPoint b₂ =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [b₂]
    rw [polynomialSectionSpecialPoint_difference, hr₁special]
    funext i
    simp [zeroPolynomialSection, polynomialSectionSpecialPoint]

  exact
    {
      rawDefect := E.defect - 2 * q
      scale := 1
      scale_pos := by omega
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := P₂
      movingSection := b₂
      hessianDefect := hdef₂
      nonlinearDegreeBound := hdegree₂
      exactCollision := hcoll₂
      sectionSpecial := hb₂special
    }

/-- A positive integral kernel slope on the actual right-recentered blocker
source gives genuine certified fixed-scale progress relative to the honest
adaptive endpoint state. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.exists_certifiedFixedScaleStrictSuccessor_of_positiveRecenteredIntegralKernelSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (q : ℕ)
    (hq : 0 < q)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility kernel q
        B.aligned.endpoint.rightRecenteredFamily) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target
        (B.aligned.toAdaptiveState s).toScaleAware := by
  let E := B.aligned.endpoint
  let target := B.recenteredKernelScaleOneTarget s kernel q hdiv hq hkernel

  have hcost : 2 * q ≤ E.defect := by
    exact
      two_mul_slope_le_of_integralKernelBlowup
        kernel q E.defect E.rightRecenteredFamily hdiv
        E.rightRecenteredFamily_hessianDefect

  have hclock : E.defect - 2 * q < E.defect := by
    omega

  refine ⟨target, ?_⟩
  apply certifiedFixedScaleEpisodeProgress_of_rawDefect_lt RR
  · rfl
  · change E.defect - 2 * q < E.defect
    exact hclock

/-! ## Recentered zero-slope obstruction -/

/-- Explicit maximal-slope-zero certificate on the actual right-recentered
source used by the blocker Schur/rigid geometry. -/
structure AdaptiveRecenteredKernelZeroSlopeObstruction
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (kernel : Fin 4) : Prop where
  active :
    IsActiveKernelCoordinate kernel
      B.aligned.endpoint.rightRecenteredFamily
  maximal_eq_zero :
    maximalIntegralKernelSlope kernel
        B.aligned.endpoint.rightRecenteredFamily active = 0

/-- Recentered zero slope means that no positive integral kernel blow-up
exists on that actual recentered source. -/
theorem AdaptiveRecenteredKernelZeroSlopeObstruction.no_positive_integral_slope
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    {kernel : Fin 4}
    (Z : AdaptiveRecenteredKernelZeroSlopeObstruction B kernel) :
    ¬ ∃ q : ℕ, 0 < q ∧
      HasIntegralKernelCoefficientDivisibility kernel q
        B.aligned.endpoint.rightRecenteredFamily := by
  exact
    no_positive_admissible_of_maximalIntegralKernelSlope_eq_zero
      kernel B.aligned.endpoint.rightRecenteredFamily
      Z.active Z.maximal_eq_zero

/-- Universal kernel normalisation on the actual right-recentered blocker
source.  The positive branch is converted all the way back into a canonical
adaptive successor; only maximal-slope-zero geometry survives. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.certifiedStrict_or_recenteredZeroSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target
        (B.aligned.toAdaptiveState s).toScaleAware) ∨
      AdaptiveRecenteredKernelZeroSlopeObstruction B kernel := by
  let hactive :
      IsActiveKernelCoordinate kernel
        B.aligned.endpoint.rightRecenteredFamily :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel B.aligned.endpoint.rightRecenteredFamily
      B.aligned.endpoint.defect
      B.aligned.endpoint.rightRecenteredFamily_hessianDefect

  rcases maximalIntegralKernelSlope_zero_or_positive
      kernel B.aligned.endpoint.rightRecenteredFamily hactive with
    hzero | hpos
  · exact Or.inr ⟨hactive, hzero.1⟩
  · left
    exact
      B.exists_certifiedFixedScaleStrictSuccessor_of_positiveRecenteredIntegralKernelSlope
        RR s kernel hkernel
        (maximalIntegralKernelSlope kernel
          B.aligned.endpoint.rightRecenteredFamily hactive)
        hpos.1 hpos.2

/-! ## Global double-normalised dispatcher -/

/-- Canonical JC2-free outcome after coordinate `3` has maximal integral
slope zero in both the adaptive endpoint family and the honest
right-recentered family used by the residual blocker geometry. -/
inductive AdaptiveAlignedSmithCanonicalRecenteredZeroSlopeOutcome
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

  | blockerZeroSchurClosingDoubleZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
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

/-- Run the common coordinate-`3` kernel normalisation on the actual
right-recentered source of every branch which survived endpoint
normalisation.  Any positive recentered slope is genuine strict progress;
therefore every remaining geometric constructor carries both zero-slope
certificates. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalRecenteredZeroSlopeDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRecenteredZeroSlopeOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalZeroSlopeDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt, Z⟩ |
    ⟨B, C, D, hwall, Z⟩ |
    ⟨B, C, Z⟩ |
    ⟨B, hall, P, hrigid, Z⟩ |
    ⟨B, hall, P, hrigid, Z⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · rcases B.certifiedStrict_or_recenteredZeroSlope
        RR s adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | ZR
    · exact .strict ⟨(B.aligned.toAdaptiveState s).toScaleAware,
        target, hprogress⟩
    · exact .blockerSchurEarlyActualLayerDoubleZeroSlope B C hlt Z ZR

  · rcases B.certifiedStrict_or_recenteredZeroSlope
        RR s adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | ZR
    · exact .strict ⟨(B.aligned.toAdaptiveState s).toScaleAware,
        target, hprogress⟩
    · exact .blockerSchurEarlierWallDoubleZeroSlope B C D hwall Z ZR

  · rcases B.certifiedStrict_or_recenteredZeroSlope
        RR s adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | ZR
    · exact .strict ⟨(B.aligned.toAdaptiveState s).toScaleAware,
        target, hprogress⟩
    · exact .blockerZeroSchurClosingDoubleZeroSlope B C Z ZR

  · rcases B.certifiedStrict_or_recenteredZeroSlope
        RR s adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | ZR
    · exact .strict ⟨(B.aligned.toAdaptiveState s).toScaleAware,
        target, hprogress⟩
    · exact .blockerPlanarRigidPacketDoubleZeroSlope B hall P hrigid Z ZR

  · rcases B.certifiedStrict_or_recenteredZeroSlope
        RR s adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | ZR
    · exact .strict ⟨(B.aligned.toAdaptiveState s).toScaleAware,
        target, hprogress⟩
    · exact .blockerWSquareRigidPacketDoubleZeroSlope B hall P hrigid Z ZR

end

end HC4.Valuation
