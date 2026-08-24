import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import Mathlib.Tactic

/-!
# A18.4.41: positive saturated slope already certifies kernel freeness

A18.4.39 consumes a saturated kernel opening once the incoming special fibre
is known to be independent of the opened coordinate.  Several late canonical
normalisers instead retain the equivalent numerical fact that the saturated
first-contact slope is positive.

The missing implication is elementary but important for sound global
termination.  If the old special fibre contained any monomial with positive
kernel exponent, that coefficient would have parameter order zero.  Its
denominator-cleared kernel slope would therefore be zero, forcing the finite
minimum saturated slope to be zero.  Hence a positive saturated slope already
proves that the special fibre is kernel-free.

This file records that implication and packages the A18.4.39 dichotomy with
no separately supplied freeness hypothesis.  No new progress measure or
homogeneity assumption is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A coefficient visible on the parameter-zero special fibre has exact
parameter order zero in the original family. -/
theorem adaptiveSourceCoefficientParameterOrder_eq_zero_of_mem_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber P).support) :
    adaptiveSourceCoefficientParameterOrder P d = 0 := by
  have hspecial :
      Polynomial.constantCoeff (MvPolynomial.coeff d P) ≠ 0 := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    simpa [coeff_polynomialFamilySpecialFiber] using hcoeff
  have hcoeff : MvPolynomial.coeff d P ≠ 0 := by
    intro hz
    apply hspecial
    simp [hz]
  simp only [adaptiveSourceCoefficientParameterOrder, dif_neg hcoeff]
  by_contra hne
  have hpos :
      0 < polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff :=
    Nat.pos_of_ne_zero hne
  have hpow :
      (Polynomial.X : Polynomial K) ∣
        Polynomial.X ^ polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff := by
    simpa using
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) 1
        (polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff)
        hpos
  have hXd :
      (Polynomial.X : Polynomial K) ∣ MvPolynomial.coeff d P :=
    dvd_trans hpow (polynomialParameterOrder_dvd _ hcoeff)
  exact hspecial (Polynomial.X_dvd_iff.mp hXd)

/-- **Positive saturated slope forces kernel freeness of the old special
fibre.**

A special-fibre monomial with positive kernel exponent would be an active
source monomial of exact parameter order zero, hence would contribute slope
zero to the finite minimum. -/
theorem specialFiber_free_of_saturatedKernelSlope_pos
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hq : 0 < saturatedKernelSlope kernel P hactive) :
    ∀ d ∈ (polynomialFamilySpecialFiber P).support,
      d kernel = 0 := by
  intro d hd
  by_contra hdk
  have hdkpos : 0 < d kernel := Nat.pos_of_ne_zero hdk
  have hspecial := MvPolynomial.mem_support_iff.mp hd
  have hcoeff : MvPolynomial.coeff d P ≠ 0 := by
    intro hz
    apply hspecial
    simp [coeff_polynomialFamilySpecialFiber, hz]
  have hdP : d ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have hdActive : d ∈ activeKernelSupport kernel P :=
    Finset.mem_filter.mpr ⟨hdP, hdkpos⟩
  have hqle :
      saturatedKernelSlope kernel P hactive ≤
        denominatorClearedCoefficientSlope kernel P d :=
    Finset.min'_le
      ((activeKernelSupport kernel P).image
        (denominatorClearedCoefficientSlope kernel P))
      (denominatorClearedCoefficientSlope kernel P d)
      (Finset.mem_image.mpr ⟨d, hdActive, rfl⟩)
  have horder : adaptiveSourceCoefficientParameterOrder P d = 0 :=
    adaptiveSourceCoefficientParameterOrder_eq_zero_of_mem_specialFiber P hd
  have hslope : denominatorClearedCoefficientSlope kernel P d = 0 := by
    simp [denominatorClearedCoefficientSlope, horder]
  rw [hslope] at hqle
  omega

/-- Positive saturated slope is therefore enough to invoke the complete
A18.4.39 first-contact dichotomy. -/
theorem ScaleAwareAdaptiveGeometricRestartState.positiveSaturatedKernelOpening_unramified_or_nonlinearHessian
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      let R := kernelSlopeDenominatorClearingRamification kernel s.family
      let q := saturatedKernelSlope kernel s.family hactive
      let Pram := parameterRamificationFamily (K := K) R s.family
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive
      let Fnext := polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)
      ∃ d ∈ Fnext.support,
        2 ≤ d kernel ∧
        MvPolynomial.pderiv kernel (MvPolynomial.pderiv kernel Fnext) ≠ 0 := by
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0 :=
    specialFiber_free_of_saturatedKernelSlope_pos
      (K := K) kernel s.family hactive hq
  exact s.saturatedKernelOpening_unramified_or_nonlinearHessian
    RR kernel hkernel hactive hfree

end

end HC4.Valuation
