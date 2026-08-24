import HC4.Valuation.AdaptiveDegreeTwoSaturatedFace
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSoundEpisodeInterface
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Ramified saturated contact -> unramified fixed-scale re-entry

The scale-aware canonical closing stack deliberately keeps a ramified kernel
opening separate from fixed-scale recursive progress.  A bare strict decrease
of `rawDefect / scale` is not a well-founded global induction coordinate.

This file isolates the arithmetic situation in which the denominator-cleared
saturated opening is in fact unnecessary.  If the saturated first-contact face
contains a monomial which is linear in the opened kernel coordinate, then the
first-contact equality forces the denominator-clearing ramification index to
divide the saturated slope.  Dividing the slope by that index produces an
honest integral kernel slope on the *unramified* source family.

We also package the corresponding kernel blow-up directly for an arbitrary
scale-aware state.  The scale is left literally unchanged, while the raw
Hessian defect drops by `2 * slope`.  Hence the resulting target is certified
same-scale episode progress and may be consumed by the existing well-founded
fixed-scale recursion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Actual same-scale target of one positive integral kernel blow-up on a
scale-aware source state.  This is the arbitrary-scale analogue of
`AdaptiveGeometricRestartState.integralKernelScaleOneTarget`. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.integralKernelSameScaleTarget
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (q : ℕ)
    (hdiv : HasIntegralKernelCoefficientDivisibility kernel q s.family)
    (hq : 0 < q)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let Pnext := integralKernelBlowupFamily kernel q s.family hdiv
  let bnext := kernelBlowupSection kernel q s.movingSection

  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (s.rawDefect - 2 * q) := by
    dsimp [Pnext]
    exact
      integralKernelBlowup_hasHessianDefect_sub
        kernel q s.rawDefect s.family hdiv s.hessianDefect

  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext := by
    dsimp [Pnext]
    exact
      nonlinearDegreeBound_integralKernelBlowup
        s.degreeCap q kernel s.family s.nonlinearDegreeBound hdiv

  have hcollRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q s.family hdiv
      (zeroPolynomialSection (K := K)) s.movingSection s.exactCollision

  have hzero :
      kernelBlowupSection kernel q (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) :=
    kernelBlowupSection_zeroPolynomialSection kernel q

  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    rw [hzero] at hcollRaw
    simpa [Pnext, bnext] using hcollRaw

  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bnext]
    exact
      polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
        kernel hq hkernel s.movingSection s.sectionSpecial

  exact
    {
      rawDefect := s.rawDefect - 2 * q
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefNext
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollNext
      sectionSpecial := hspecialNext
    }

/-- A positive integral transverse kernel slope on an arbitrary scale-aware
state is genuine fixed-scale recursive progress. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_certifiedSameScaleStrictSuccessor_of_positiveIntegralKernelSlope
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (q : ℕ)
    (hq : 0 < q)
    (hdiv : HasIntegralKernelCoefficientDivisibility kernel q s.family) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedSameScaleEpisodeProgress RR target s := by
  let target := s.integralKernelSameScaleTarget kernel q hdiv hq hkernel

  have hcost : 2 * q ≤ s.rawDefect :=
    two_mul_slope_le_of_integralKernelBlowup
      kernel q s.rawDefect s.family hdiv s.hessianDefect

  have hclock : s.rawDefect - 2 * q < s.rawDefect := by
    omega

  refine ⟨target, ?_⟩
  apply certifiedSameScaleEpisodeProgress_of_rawDefect_lt RR
  · rfl
  · change s.rawDefect - 2 * q < s.rawDefect
    exact hclock

/-- If the denominator-cleared saturated slope is a multiple of the common
ramification index, then dividing by that index gives an integral kernel slope
on the original, unramified family. -/
theorem saturatedKernelSlope_unramifies_of_eq_ramification_mul
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (m : ℕ)
    (hqm :
      saturatedKernelSlope kernel P hactive =
        kernelSlopeDenominatorClearingRamification kernel P * m) :
    HasIntegralKernelCoefficientDivisibility kernel m P := by
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos kernel P
  intro d hdP
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdP
  by_cases hd0 : d kernel = 0
  · simp [kernelCoefficientTauPower, hd0]
  · have hdActive : d ∈ activeKernelSupport kernel P := by
      exact Finset.mem_filter.mpr ⟨hdP, Nat.pos_of_ne_zero hd0⟩
    have hqle : q ≤ denominatorClearedCoefficientSlope kernel P d := by
      exact Finset.min'_le
        ((activeKernelSupport kernel P).image
          (denominatorClearedCoefficientSlope kernel P))
        (denominatorClearedCoefficientSlope kernel P d)
        (Finset.mem_image.mpr ⟨d, hdActive, rfl⟩)
    have hexpRam :
        q * d kernel ≤
          R * adaptiveSourceCoefficientParameterOrder P d := by
      have hmul := Nat.mul_le_mul_right (d kernel) hqle
      unfold denominatorClearedCoefficientSlope at hmul
      exact le_trans hmul (Nat.div_mul_le_self _ _)
    have hexpMul :
        R * (m * d kernel) ≤
          R * adaptiveSourceCoefficientParameterOrder P d := by
      dsimp [q, R] at hexpRam ⊢
      rw [hqm] at hexpRam
      simpa [Nat.mul_assoc] using hexpRam
    have hexp :
        m * d kernel ≤ adaptiveSourceCoefficientParameterOrder P d := by
      exact Nat.le_of_mul_le_mul_left hexpMul hRpos
    have horder :
        adaptiveSourceCoefficientParameterOrder P d =
          polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
      simp [adaptiveSourceCoefficientParameterOrder, hcoeffne]
    have hpow :
        (Polynomial.X ^ (m * d kernel) : Polynomial K) ∣
          Polynomial.X ^
            (adaptiveSourceCoefficientParameterOrder P d) := by
      exact polynomial_X_pow_dvd_X_pow_of_le
        (K := K) _ _ hexp
    unfold kernelCoefficientTauPower
    exact dvd_trans hpow (by
      rw [horder]
      exact polynomialParameterOrder_dvd _ hcoeffne)

/-- **Linear first contact unramifies the saturated opening.**

Suppose the special fibre of the denominator-cleared saturated kernel blow-up
contains a first-contact monomial having kernel exponent exactly one.  The
contact equation reads

    q * 1 = R * nu,

so `q = R * nu`.  Thus the saturated rational slope is already the integral
slope `nu` on the original source family. -/
theorem saturatedKernelSlope_unramifiedData_of_linearFirstContact
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        d kernel = 0)
    (d : Fin 4 →₀ ℕ)
    (hd :
      let R := kernelSlopeDenominatorClearingRamification kernel P
      let q := saturatedKernelSlope kernel P hactive
      let Pram := parameterRamificationFamily (K := K) R P
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel P hactive
      d ∈ (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily kernel q Pram hdiv)).support)
    (hd1 : d kernel = 1) :
    ∃ m : ℕ,
      0 < m ∧
      saturatedKernelSlope kernel P hactive =
        kernelSlopeDenominatorClearingRamification kernel P * m ∧
      HasIntegralKernelCoefficientDivisibility kernel m P := by
  let R := kernelSlopeDenominatorClearingRamification kernel P
  let q := saturatedKernelSlope kernel P hactive
  have hRpos : 0 < R :=
    kernelSlopeDenominatorClearingRamification_pos kernel P
  have hqpos : 0 < q :=
    saturatedKernelSlope_pos kernel P hactive hfree
  have hcontact :=
    (mem_specialFiber_saturatedKernelBlowup_iff
      (K := K) kernel P hactive d).mp hd
  let m := adaptiveSourceCoefficientParameterOrder P d
  have hqm : q = R * m := by
    dsimp [q, R, m]
    simpa [hd1] using hcontact.2
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hq0 : q = 0 := by
      calc
        q = R * m := hqm
        _ = 0 := by simp [hm0]
    exact (Nat.ne_of_gt hqpos) hq0
  have hdiv : HasIntegralKernelCoefficientDivisibility kernel m P := by
    apply saturatedKernelSlope_unramifies_of_eq_ramification_mul
      (K := K) kernel P hactive m
    simpa [q, R] using hqm
  exact ⟨m, hmpos, by simpa [q, R] using hqm, hdiv⟩

/-- **Unramified re-entry theorem.**

A kernel-linear monomial on the saturated first-contact face converts the
would-be scale-changing restart into an ordinary same-scale strict successor.
No recursion on the positive-rational scaled defect is needed in this branch. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_unramifiedReentry_of_saturatedLinearFirstContact
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0)
    (d : Fin 4 →₀ ℕ)
    (hd :
      let R := kernelSlopeDenominatorClearingRamification kernel s.family
      let q := saturatedKernelSlope kernel s.family hactive
      let Pram := parameterRamificationFamily (K := K) R s.family
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive
      d ∈ (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily kernel q Pram hdiv)).support)
    (hd1 : d kernel = 1) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedSameScaleEpisodeProgress RR target s := by
  rcases saturatedKernelSlope_unramifiedData_of_linearFirstContact
      (K := K) kernel s.family hactive hfree d hd hd1 with
    ⟨m, hmpos, _hqm, hdiv⟩
  exact s.exists_certifiedSameScaleStrictSuccessor_of_positiveIntegralKernelSlope
    RR kernel hkernel m hmpos hdiv

end

end HC4.Valuation
