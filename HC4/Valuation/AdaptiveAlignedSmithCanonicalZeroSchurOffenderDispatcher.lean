import HC4.Valuation.AdaptiveAlignedSmithCanonicalRecenteredZeroSlopeDispatcher
import HC4.Valuation.AdaptiveCoefficientOrder
import Mathlib.Tactic

/-!
# Canonical zero-Schur branch as an explicit source first-kernel offender

The double zero-slope dispatcher has put the residual blocker geometry in the
correct source presentation.  In particular, on a zero-Schur closing we now
know that the honest right-recentered family admits no positive integral
coordinate-`3` kernel slope.

But an exact zero-Schur clock has a positive first common order `e`.  Testing
that candidate slope against the *actual source family* therefore cannot land
in the integral branch: otherwise `e > 0` itself would be a positive
admissible recentered kernel slope, contradicting the retained zero-slope
certificate.

Finite source support consequently forces a concrete monomial `d` with

    ord_tau(coeff_d Q) < e * d_3.

This file packages that monomial as a source-level first-kernel offender and
promotes the global dispatcher so that the old bare zero-Schur closing
constructor disappears.  The remaining zero-Schur output now carries the
exact supported coefficient which reaches the source lattice strictly before
the Schur candidate kernel ray.

No homogeneity, terminal extraction, or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Generic finite-support source offender arithmetic -/

/-- Nondivisibility by the kernel power required at a proposed slope is
exactly a strict shortfall of the proof-independent parameter order of that
supported source coefficient. -/
theorem adaptiveSupportOffender_parameterOrder_lt_required
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support)
    (hfail :
      ¬ kernelCoefficientTauPower (K := K) kernel slope d ∣
        MvPolynomial.coeff d P) :
    adaptiveSourceCoefficientParameterOrder P d < slope * d kernel := by
  have hne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  unfold adaptiveSourceCoefficientParameterOrder
  rw [dif_neg hne]
  by_contra hnot
  have hreq :
      slope * d kernel ≤
        polynomialParameterOrder (MvPolynomial.coeff d P) hne := by
    omega
  have hpow :
      (Polynomial.X ^ (slope * d kernel) : Polynomial K) ∣
        Polynomial.X ^
          (polynomialParameterOrder (MvPolynomial.coeff d P) hne) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K)
      (slope * d kernel)
      (polynomialParameterOrder (MvPolynomial.coeff d P) hne)
      hreq
  have hcoeff :
      Polynomial.X ^
          (polynomialParameterOrder (MvPolynomial.coeff d P) hne) ∣
        MvPolynomial.coeff d P :=
    polynomialParameterOrder_dvd (MvPolynomial.coeff d P) hne
  apply hfail
  unfold kernelCoefficientTauPower
  exact dvd_trans hpow hcoeff

/-- Finite-support dichotomy at one proposed positive kernel slope, expressed
in the numerical order form needed by the first-wall/restart layer. -/
theorem integralKernelDivisibility_or_adaptiveSupportOffender
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasIntegralKernelCoefficientDivisibility kernel slope P ∨
      ∃ d ∈ P.support,
        adaptiveSourceCoefficientParameterOrder P d < slope * d kernel := by
  classical
  by_cases hdiv : HasIntegralKernelCoefficientDivisibility kernel slope P
  · exact Or.inl hdiv
  · right
    unfold HasIntegralKernelCoefficientDivisibility at hdiv
    push_neg at hdiv
    rcases hdiv with ⟨d, hd, hfail⟩
    exact ⟨d, hd,
      adaptiveSupportOffender_parameterOrder_lt_required
        kernel slope P d hd hfail⟩

/-! ## Honest zero-Schur first-kernel offender -/

/-- Concrete source coefficient which blocks the first integral kernel stage
suggested by the exact zero-Schur clock.

The witness lives in the honest right-recentered polynomial family, not in a
matrix specialization.  The strict shortfall itself forces positive
coordinate-`3` degree, exactly as in the legacy first-kernel stage, but we keep
the certificate in the minimal existential form so it remains a pure `Prop`
and does not introduce a new data carrier. -/
def AdaptiveAlignedSmithZeroSchurFirstKernelOffender
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) : Prop :=
  ∃ d ∈ C.family.support,
    adaptiveSourceCoefficientParameterOrder C.family d <
      C.chartData.zeroData.toClock.firstOrder *
        d adaptiveCanonicalCommonKernel

namespace AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-- Under recentered zero slope, the positive first zero-Schur order cannot be
an integral source-kernel slope.  Hence a concrete supported source offender
is forced. -/
theorem firstKernelOffender_of_recenteredZeroSlope
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (ZR : AdaptiveRecenteredKernelZeroSlopeObstruction
      B adaptiveCanonicalCommonKernel) :
    AdaptiveAlignedSmithZeroSchurFirstKernelOffender C := by
  let e := C.chartData.zeroData.toClock.firstOrder
  have he : 0 < e := C.chartData.zeroData.toClock.firstOrder_pos

  rcases integralKernelDivisibility_or_adaptiveSupportOffender
      (K := K) adaptiveCanonicalCommonKernel e C.family with
    hdiv | ⟨d, hd, hlt⟩

  · have hdiv' :
        HasIntegralKernelCoefficientDivisibility
          adaptiveCanonicalCommonKernel e
          B.aligned.endpoint.rightRecenteredFamily := by
      simpa [AdaptiveAlignedSmithZeroSchurClosingSourceCarrier.family] using hdiv
    exact False.elim
      (ZR.no_positive_integral_slope ⟨e, he, hdiv'⟩)

  · exact ⟨d, hd, by simpa [e] using hlt⟩

/-- The clock candidate is therefore genuinely nonintegral on the honest
recentered source. -/
theorem firstKernelOffender_not_candidateDivisibility
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
    (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C) :
    ¬ HasIntegralKernelCoefficientDivisibility
        adaptiveCanonicalCommonKernel
        C.chartData.zeroData.toClock.firstOrder
        C.family := by
  intro hdiv
  unfold AdaptiveAlignedSmithZeroSchurFirstKernelOffender at O
  rcases O with ⟨d, hd, hlt⟩
  have hdvd := hdiv d hd
  have hne : MvPolynomial.coeff d C.family ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hle :
      C.chartData.zeroData.toClock.firstOrder *
          d adaptiveCanonicalCommonKernel ≤
        polynomialParameterOrder
          (MvPolynomial.coeff d C.family) hne := by
    exact
      polynomial_X_pow_dvd_le_parameterOrder
        (MvPolynomial.coeff d C.family) hne
        (C.chartData.zeroData.toClock.firstOrder *
          d adaptiveCanonicalCommonKernel)
        (by simpa [kernelCoefficientTauPower] using hdvd)
  unfold adaptiveSourceCoefficientParameterOrder at hlt
  rw [dif_neg hne] at hlt
  omega

end AdaptiveAlignedSmithZeroSchurClosingSourceCarrier

/-! ## Global dispatcher with the bare zero-Schur closing removed -/

/-- Canonical double-zero-slope outcome after resolving every zero-Schur
closing to an explicit first-kernel source offender. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurOffenderOutcome
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

  | blockerZeroSchurFirstKernelOffender
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
      (O : AdaptiveAlignedSmithZeroSchurFirstKernelOffender C)
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

/-- Run the double-zero-slope dispatcher and discharge the integral side of
the zero-Schur first-kernel test.  Thus the global frontier no longer contains
a bare zero-Schur closing: its source-level coefficient obstruction is exposed
immediately. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalZeroSchurOffenderDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalZeroSchurOffenderOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalRecenteredZeroSlopeDispatcher
      RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt, Z, ZR⟩ |
    ⟨B, C, D, hwall, Z, ZR⟩ |
    ⟨B, C, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩ |
    ⟨B, hall, P, hrigid, Z, ZR⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero
  · exact .blockerSchurEarlyActualLayerDoubleZeroSlope B C hlt Z ZR
  · exact .blockerSchurEarlierWallDoubleZeroSlope B C D hwall Z ZR
  · exact .blockerZeroSchurFirstKernelOffender
      B C (C.firstKernelOffender_of_recenteredZeroSlope ZR) Z ZR
  · exact .blockerPlanarRigidPacketDoubleZeroSlope B hall P hrigid Z ZR
  · exact .blockerWSquareRigidPacketDoubleZeroSlope B hall P hrigid Z ZR

end

end HC4.Valuation
