import HC4.Valuation.CanonicalSmithReesSpecialFiber
import HC4.Valuation.PrimitiveSmithEndpoint
import HC4.Valuation.DefectRetainingDepartureFrontier
import Mathlib.Tactic

/-!
# Defect-preserving canonical Smith exposure

The original determinant parameter and the Smith separator are distinct
filtrations.  The special-fibre Smith-Rees family from Phase 75.9 exposes the
persistent packet honestly, but by itself it has lost the positive Hessian
defect clock.

This file folds the two clocks back into one parameter in the canonical
aligned way:

* ramify the original parameter by `20`;
* take one symmetric Smith step `(2,2)`;
* divide by the conformal multiplier `X^4`.

For a source coefficient of exact parameter order `v` and symmetric Smith
derivative `delta`, the residual order is

    20 * v + delta.

If `v = 0`, the monomial lies on the original special fibre and the retained
symmetric-minimal geometry gives `delta >= 0`.  If `v > 0`, the universal
Smith bound `delta >= -4` makes the residual order strictly positive.
Consequently the transformation is integral, preserves the pure Hessian
defect (now on the ramified clock `20 * Delta`), and has special fibre
*exactly* the canonical Smith packet.

This is the one-parameter family consumed by the matrix Schur clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! -----------------------------------------------------------------------
  Exact order zero and the special fibre
------------------------------------------------------------------------ -/

/-- For a supported source monomial, exact parameter order zero is
precisely survival on the polynomial-family special fibre. -/
theorem smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    smithFamilyCoefficientOrder P d = 0 ↔
      d ∈ (polynomialFamilySpecialFiber P).support := by
  constructor
  · intro horder
    have hconst :=
      constantCoeff_ne_zero_of_smithFamilyCoefficientOrder_eq_zero
        P hd horder
    exact
      (mem_polynomialFamilySpecialFiber_support_iff P d).2
        ⟨hd, hconst⟩
  · intro hspecial
    rcases
        (mem_polynomialFamilySpecialFiber_support_iff P d).1 hspecial with
      ⟨_hd, hconst⟩
    by_contra horder
    have hpos : 0 < smithFamilyCoefficientOrder P d :=
      Nat.pos_of_ne_zero horder
    have hpow :
        Polynomial.X ^ (smithFamilyCoefficientOrder P d) ∣
          MvPolynomial.coeff d P :=
      smithFamilyCoefficientOrder_dvd P hd
    have hsmall :
        (Polynomial.X ^ 1 : Polynomial K) ∣
          Polynomial.X ^ (smithFamilyCoefficientOrder P d) :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) 1 _ (by omega)
    have hX : Polynomial.X ∣ MvPolynomial.coeff d P := by
      simpa using dvd_trans hsmall hpow
    have hzero :
        Polynomial.constantCoeff (MvPolynomial.coeff d P) = 0 := by
      exact Polynomial.X_dvd_iff.mp hX
    exact hconst hzero

/-! -----------------------------------------------------------------------
  One canonical aligned Smith step is always integral at the frontier
------------------------------------------------------------------------ -/

/-- At a canonical lossless frontier, one symmetric Smith step after the
fixed ramification by twenty has nonnegative residual order on every source
coefficient. -/
theorem CanonicalSmithLosslessFrontier.oneStepSmith_coefficient_nonnegative
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    ∀ d ∈ f.family.support,
      0 ≤
        alignedSmithCoefficientValue
          (smithFamilyCoefficientOrder f.family d)
          1
          (smithSeparatorDelta 1 1 (smithAxisProjection d)) := by
  intro d hd
  let v := smithFamilyCoefficientOrder f.family d
  by_cases hv : v = 0
  · have hdSpecial :
        d ∈ (polynomialFamilySpecialFiber f.family).support := by
      exact
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          f.family hd).1 (by simpa [v] using hv)
    have hdelta :=
      f.specialFiber_symmetricDelta_nonnegative d hdSpecial
    apply
      alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
        v 1 (smithSeparatorDelta 1 1 (smithAxisProjection d))
    simpa [smithAxisProjection] using hdelta
  · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    by_cases hneg :
        smithSeparatorDelta 1 1 (smithAxisProjection d) < 0
    · rcases
        smithSeparatorDelta_one_one_negative_cases
          (smithAxisProjection d) hneg with h4 | h2
      · rw [h4]
        exact
          alignedSmithCoefficientValue_neg_four_nonnegative
            v 1 (by omega)
      · rw [h2]
        exact
          alignedSmithCoefficientValue_neg_two_nonnegative
            v 1 (by omega)
    · have hdelta :
          0 ≤ smithSeparatorDelta 1 1 (smithAxisProjection d) := by
        omega
      exact
        alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
          v 1 _ hdelta

/-- Exact coefficient divisibility for the defect-preserving one-step Smith
exposure. -/
theorem CanonicalSmithLosslessFrontier.oneStepSmith_integralCoefficients
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    HasIntegralSmithConformalCoefficientDivisibility
      2 2
      (parameterRamificationFamily
        (K := K) alignedSmithRamificationIndex f.family) := by
  simpa using
    (alignedSmith_coefficientDivisibility_of_nonnegative
      (K := K) f.family 1
      f.oneStepSmith_coefficient_nonnegative)

/-! -----------------------------------------------------------------------
  Defect-preserving Smith exposure family
------------------------------------------------------------------------ -/

/-- Ramify the true determinant clock by twenty and then take exactly one
integral symmetric Smith step. -/
noncomputable def CanonicalSmithLosslessFrontier.defectSmithExposureFamily
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  integralSmithConformalFamily
    2 2
    (parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex f.family)
    f.oneStepSmith_integralCoefficients

/-- Departure frontiers use the exposure family of their retained lossless
Smith geometry. -/
noncomputable def CanonicalSmithDepartureFrontier.defectSmithExposureFamily
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  f.lossless.defectSmithExposureFamily

/-- The exposure keeps the exact Hessian determinant clock, merely ramified
by the canonical factor `20`. -/
theorem CanonicalSmithDepartureFrontier.defectSmithExposure_hessianDefect
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      f.defectSmithExposureFamily
      (alignedSmithRamificationIndex * f.defect) := by
  have hram :
      HasPolynomialFamilyHessianDefect
        (K := K)
        (parameterRamificationFamily
          (K := K) alignedSmithRamificationIndex f.lossless.family)
        (alignedSmithRamificationIndex * f.defect) :=
    parameterRamificationFamily_hasHessianDefect
      alignedSmithRamificationIndex f.defect
      f.lossless.family f.hessianDefect
  unfold CanonicalSmithDepartureFrontier.defectSmithExposureFamily
  unfold CanonicalSmithLosslessFrontier.defectSmithExposureFamily
  exact
    integralSmithConformalFamily_preservesHessianDefect
      2 2 (alignedSmithRamificationIndex * f.defect)
      (parameterRamificationFamily
        (K := K) alignedSmithRamificationIndex f.lossless.family)
      f.lossless.oneStepSmith_integralCoefficients
      hram

/-! -----------------------------------------------------------------------
  Exact residual exponent and coefficient formula
------------------------------------------------------------------------ -/

/-- Natural residual order after ramification by twenty and one symmetric
Smith step.  Integrality proves the subtraction does not truncate on actual
support. -/
def canonicalOneStepSmithResidualExponent
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ :=
  smithConformalRawExponent 2 2 d +
      alignedSmithRamificationIndex * smithFamilyCoefficientOrder P d - 4

/-- On source support, the residual natural exponent is zero exactly when
both clocks are zero: source parameter order zero and Smith separator zero. -/
theorem CanonicalSmithLosslessFrontier.oneStepResidual_eq_zero_iff
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ f.family.support) :
    canonicalOneStepSmithResidualExponent f.family d = 0 ↔
      smithFamilyCoefficientOrder f.family d = 0 ∧
      smithSeparatorDelta 1 1 (smithAxisProjection d) = 0 := by
  have hlegal := f.oneStepSmith_coefficient_nonnegative d hd
  have hclock := smithSeparatorDelta_projection_eq_raw_sub_four d
  have hle :
      4 ≤ smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder f.family d := by
    unfold alignedSmithCoefficientValue at hlegal
    rw [hclock] at hlegal
    norm_num [alignedSmithRamificationIndex] at hlegal ⊢
    omega
  constructor
  · intro hzero
    unfold canonicalOneStepSmithResidualExponent at hzero
    have htotal :
        smithConformalRawExponent 2 2 d +
            alignedSmithRamificationIndex *
              smithFamilyCoefficientOrder f.family d = 4 := by
      omega
    have hv : smithFamilyCoefficientOrder f.family d = 0 := by
      norm_num [alignedSmithRamificationIndex] at htotal
      omega
    have hraw : smithConformalRawExponent 2 2 d = 4 := by
      rw [hv] at htotal
      simpa using htotal
    have hdelta :
        smithSeparatorDelta 1 1 (smithAxisProjection d) = 0 := by
      rw [hclock, hraw]
      norm_num
    exact ⟨hv, hdelta⟩
  · rintro ⟨hv, hdelta⟩
    have hrawZ : (smithConformalRawExponent 2 2 d : ℤ) = 4 := by
      rw [hdelta] at hclock
      omega
    have hraw : smithConformalRawExponent 2 2 d = 4 := by
      exact_mod_cast hrawZ
    unfold canonicalOneStepSmithResidualExponent
    simp [hv, hraw]

/-- Exact coefficient formula for the defect-preserving exposure family.
The chosen Smith quotient is the ramified primitive source coefficient,
multiplied by precisely the residual parameter power. -/
theorem CanonicalSmithLosslessFrontier.defectSmithExposure_coefficient
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ f.family.support) :
    MvPolynomial.coeff d f.defectSmithExposureFamily =
      Polynomial.X ^
          (canonicalOneStepSmithResidualExponent f.family d) *
        parameterRamificationHom
          (K := K) alignedSmithRamificationIndex
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d f.family)
            (MvPolynomial.mem_support_iff.mp hd)) := by
  let P := f.family
  let Pram :=
    parameterRamificationFamily
      (K := K) alignedSmithRamificationIndex P
  let hsmith := f.oneStepSmith_integralCoefficients
  have hdRam : d ∈ Pram.support := by
    dsimp [Pram, P]
    exact mem_parameterRamificationFamily_support_of_mem f.family hd
  have hcoeff :
      MvPolynomial.coeff d f.defectSmithExposureFamily =
        smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
    unfold CanonicalSmithLosslessFrontier.defectSmithExposureFamily
    exact
      coeff_integralSmithConformalFamily_of_mem
        2 2 Pram hsmith hdRam
  rw [hcoeff]
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      2 2 Pram hsmith hdRam
  have hfactor :=
    alignedRamification_sourceCoefficient_factorisation
      f.family hd
  let v := smithFamilyCoefficientOrder f.family d
  have hv :
      v =
        polynomialParameterOrder
          (MvPolynomial.coeff d f.family)
          (MvPolynomial.mem_support_iff.mp hd) := by
    dsimp [v]
    exact smithFamilyCoefficientOrder_eq f.family hd
  have hfactor' :
      MvPolynomial.coeff d Pram =
        Polynomial.X ^ (alignedSmithRamificationIndex * v) *
          parameterRamificationHom
            (K := K) alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d f.family)
              (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [Pram, P, hv] using hfactor
  have hlegal := f.oneStepSmith_coefficient_nonnegative d hd
  have hclock := smithSeparatorDelta_projection_eq_raw_sub_four d
  have hlegal' :
      (0 : ℤ) ≤
        (alignedSmithRamificationIndex : ℤ) *
            (smithFamilyCoefficientOrder f.family d : ℤ) +
          ((smithConformalRawExponent 2 2 d : ℤ) - 4) := by
    unfold alignedSmithCoefficientValue at hlegal
    rw [hclock] at hlegal
    simpa using hlegal
  have hle0 :
      4 ≤ smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex *
          smithFamilyCoefficientOrder f.family d := by
    norm_num [alignedSmithRamificationIndex] at hlegal' ⊢
    omega
  have hle :
      4 ≤ smithConformalRawExponent 2 2 d +
        alignedSmithRamificationIndex * v := by
    simpa [v] using hle0
  let r :=
    canonicalOneStepSmithResidualExponent f.family d
  have hr0 :
      4 + canonicalOneStepSmithResidualExponent f.family d =
        smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex *
            smithFamilyCoefficientOrder f.family d := by
    unfold canonicalOneStepSmithResidualExponent
    exact Nat.add_sub_of_le hle0
  have hr :
      4 + r =
        smithConformalRawExponent 2 2 d +
          alignedSmithRamificationIndex * v := by
    simpa [r, v] using hr0
  have heq :
      Polynomial.X ^ 4 *
          (Polynomial.X ^ r *
            parameterRamificationHom
              (K := K) alignedSmithRamificationIndex
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d f.family)
                (MvPolynomial.mem_support_iff.mp hd))) =
        Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
    calc
      Polynomial.X ^ 4 *
          (Polynomial.X ^ r *
            parameterRamificationHom
              (K := K) alignedSmithRamificationIndex
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d f.family)
                (MvPolynomial.mem_support_iff.mp hd))) =
        Polynomial.X ^ (4 + r) *
          parameterRamificationHom
            (K := K) alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d f.family)
              (MvPolynomial.mem_support_iff.mp hd)) := by
          rw [pow_add]
          ring
      _ =
        Polynomial.X ^
            (smithConformalRawExponent 2 2 d +
              alignedSmithRamificationIndex * v) *
          parameterRamificationHom
            (K := K) alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d f.family)
              (MvPolynomial.mem_support_iff.mp hd)) := by
          rw [hr]
      _ =
        Polynomial.X ^ (smithConformalRawExponent 2 2 d) *
          (Polynomial.X ^ (alignedSmithRamificationIndex * v) *
            parameterRamificationHom
              (K := K) alignedSmithRamificationIndex
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d f.family)
                (MvPolynomial.mem_support_iff.mp hd))) := by
          rw [pow_add]
          ring
      _ =
        smithConformalCoefficientFactor (K := K) 2 2 d *
          MvPolynomial.coeff d Pram := by
          rw [smithConformalCoefficientFactor_two_two, hfactor']
      _ =
        smithConformalMultiplier (K := K) 2 2 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := hspec
      _ =
        Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
          simp [smithConformalMultiplier,
            smithConformalMultiplierExponent]
  have hcancel := polynomial_X_pow_mul_cancel (K := K) 4 heq
  simpa [r] using hcancel.symm

/-- Constant coefficient of a supported exposure coefficient: it is the old
special-fibre coefficient exactly at residual order zero and otherwise
vanishes. -/
theorem CanonicalSmithLosslessFrontier.constantCoeff_defectSmithExposure_coefficient
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ f.family.support) :
    Polynomial.constantCoeff
        (MvPolynomial.coeff d f.defectSmithExposureFamily) =
      if canonicalOneStepSmithResidualExponent f.family d = 0 then
        Polynomial.constantCoeff (MvPolynomial.coeff d f.family)
      else 0 := by
  rw [f.defectSmithExposure_coefficient hd]
  by_cases hres : canonicalOneStepSmithResidualExponent f.family d = 0
  · have hclocks := (f.oneStepResidual_eq_zero_iff hd).1 hres
    have hv := hclocks.1
    have hv' :
        polynomialParameterOrder
          (MvPolynomial.coeff d f.family)
          (MvPolynomial.mem_support_iff.mp hd) = 0 := by
      calc
        polynomialParameterOrder
            (MvPolynomial.coeff d f.family)
            (MvPolynomial.mem_support_iff.mp hd) =
          smithFamilyCoefficientParameterOrder f.family d hd := rfl
        _ = smithFamilyCoefficientOrder f.family d :=
          (smithFamilyCoefficientOrder_eq f.family hd).symm
        _ = 0 := hv
    have hprimitive :=
      polynomialParameterPrimitivePart_spec
        (MvPolynomial.coeff d f.family)
        (MvPolynomial.mem_support_iff.mp hd)
    rw [hv'] at hprimitive
    simp only [pow_zero, one_mul] at hprimitive
    rw [hres]
    simp only [if_pos, pow_zero, one_mul]
    rw [constantCoeff_parameterRamificationHom
      alignedSmithRamificationIndex
      alignedSmithRamificationIndex_pos]
    rw [← hprimitive]
  · have hpos : 0 < canonicalOneStepSmithResidualExponent f.family d :=
      Nat.pos_of_ne_zero hres
    rw [if_neg hres]
    change
      (Polynomial.X ^ canonicalOneStepSmithResidualExponent f.family d *
          parameterRamificationHom
            (K := K) alignedSmithRamificationIndex
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d f.family)
              (MvPolynomial.mem_support_iff.mp hd))).coeff 0 = 0
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hpos]

/-- Coefficients of a polynomial-family special fibre are the constant
coefficients of the corresponding family coefficients.  Keeping this as a
separate lemma lets packet-exposure proofs rewrite only the intended special
fibre instead of unfolding every occurrence in the goal. -/
theorem coeff_polynomialFamilySpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (polynomialFamilySpecialFiber P) =
      Polynomial.constantCoeff (MvPolynomial.coeff d P) := by
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.coeff_map]

/-! -----------------------------------------------------------------------
  Exact packet exposure
------------------------------------------------------------------------ -/

/-- **Defect-preserving Smith exposure theorem.**
The special fibre of the ramified one-step Smith family is exactly the
canonical Smith packet retained by the lossless frontier. -/
theorem CanonicalSmithLosslessFrontier.specialFiber_defectSmithExposure_eq_packet
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    polynomialFamilySpecialFiber f.defectSmithExposureFamily =
      f.packet := by
  classical
  apply MvPolynomial.ext
  intro d
  unfold CanonicalSmithLosslessFrontier.packet
  unfold canonicalSpecialFiberSmithPolynomial
  rw [coeff_smithSubfacePolynomial]
  by_cases hd : d ∈ f.family.support
  · rw [coeff_polynomialFamilySpecialFiber]
    rw [f.constantCoeff_defectSmithExposure_coefficient hd]
    by_cases hdSpecial :
        d ∈ (polynomialFamilySpecialFiber f.family).support
    · have hv : smithFamilyCoefficientOrder f.family d = 0 :=
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          f.family hd).2 hdSpecial
      have hproj :
          smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
            smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber f.family) := by
        unfold smithProjectedSupport
        exact Finset.mem_image.mpr ⟨d, hdSpecial, rfl⟩
      by_cases hdelta :
          smithSeparatorDelta 1 1 (smithAxisProjection d) = 0
      · have hmem :
            smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
              canonicalSpecialFiberSmithSubface
                (polynomialFamilySpecialFiber f.family) := by
          unfold canonicalSpecialFiberSmithSubface
          exact
            (mem_smithSymmetricBalancedSubface).2
              ⟨hproj, rfl, by simpa [smithAxisProjection] using hdelta⟩
        have hres :
            canonicalOneStepSmithResidualExponent f.family d = 0 :=
          (f.oneStepResidual_eq_zero_iff hd).2 ⟨hv, hdelta⟩
        simp [hres, hmem, coeff_polynomialFamilySpecialFiber]
      · have hnot :
            smithSupportExponentOf (1 : Fin 4) 2 3 d ∉
              canonicalSpecialFiberSmithSubface
                (polynomialFamilySpecialFiber f.family) := by
          intro hmem
          unfold canonicalSpecialFiberSmithSubface at hmem
          have hmemData := (mem_smithSymmetricBalancedSubface).1 hmem
          have hz := hmemData.2.2
          exact hdelta (by simpa [smithAxisProjection] using hz)
        have hres :
            canonicalOneStepSmithResidualExponent f.family d ≠ 0 := by
          intro hz
          exact hdelta ((f.oneStepResidual_eq_zero_iff hd).1 hz).2
        simp [hres, hnot]
    · have hv : smithFamilyCoefficientOrder f.family d ≠ 0 := by
        intro hz
        exact hdSpecial
          ((smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
            f.family hd).1 hz)
      have hres :
          canonicalOneStepSmithResidualExponent f.family d ≠ 0 := by
        intro hz
        exact hv ((f.oneStepResidual_eq_zero_iff hd).1 hz).1
      have hcoeffSpecial :
          MvPolynomial.coeff d
            (polynomialFamilySpecialFiber f.family) = 0 := by
        by_contra hc
        exact hdSpecial (MvPolynomial.mem_support_iff.mpr hc)
      simp [hres, hcoeffSpecial]
  · have hdRam :
        d ∉
          (parameterRamificationFamily
            (K := K) alignedSmithRamificationIndex f.family).support := by
      intro hram
      exact hd
        ((MvPolynomial.support_map_subset
          (parameterRamificationHom
            (K := K) alignedSmithRamificationIndex)
          f.family) hram)
    have hdExposure : d ∉ f.defectSmithExposureFamily.support := by
      intro hexp
      apply hdRam
      exact
        support_integralSmithConformalFamily_subset
          2 2
          (parameterRamificationFamily
            (K := K) alignedSmithRamificationIndex f.family)
          f.oneStepSmith_integralCoefficients
          hexp
    have hcoeffExposure :
        MvPolynomial.coeff d f.defectSmithExposureFamily = 0 := by
      by_contra hc
      exact hdExposure (MvPolynomial.mem_support_iff.mpr hc)
    have hcoeffSpecial :
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber f.family) = 0 := by
      unfold polynomialFamilySpecialFiber
      rw [MvPolynomial.coeff_map]
      have hc : MvPolynomial.coeff d f.family = 0 := by
        by_contra hne
        exact hd (MvPolynomial.mem_support_iff.mpr hne)
      rw [hc]
      simp
    rw [coeff_polynomialFamilySpecialFiber, hcoeffExposure]
    simp [hcoeffSpecial]

/-- The same exact packet exposure, stated on a departure frontier. -/
theorem CanonicalSmithDepartureFrontier.specialFiber_defectSmithExposure_eq_packet
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    polynomialFamilySpecialFiber f.defectSmithExposureFamily =
      f.lossless.packet := by
  exact f.lossless.specialFiber_defectSmithExposure_eq_packet

/-! -----------------------------------------------------------------------
  Immediate canonical-outcome split
------------------------------------------------------------------------ -/

/-- At a departure frontier, the pre-existing canonical rank-two outcome is
already genuine repair progress.  Otherwise the rigid packet is now exposed
as the literal special fibre of a family which still carries a pure Hessian
defect clock. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidDefectExposure
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    (HasRankTwoPacketEscalation
        (0 : Fin 4) 1 2 D f.lossless.packet ∧
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
    (HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet ∧
      HasPolynomialFamilyHessianDefect
        (K := K)
        f.defectSmithExposureFamily
        (alignedSmithRamificationIndex * f.defect) ∧
      polynomialFamilySpecialFiber f.defectSmithExposureFamily =
        f.lossless.packet) := by
  rcases f.lossless.canonicalOutcome with hrigid | hrepair
  · exact Or.inr
      ⟨hrigid,
        f.defectSmithExposure_hessianDefect,
        f.specialFiber_defectSmithExposure_eq_packet⟩
  · exact Or.inl hrepair

/-- In the rigid branch, the retained quadratic packet carries one of the
two concrete pivot charts consumed by the polynomial Schur alignment layer. -/
theorem CanonicalSmithDepartureFrontier.rigidPacket_pivot
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hrigid :
      HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet) :
    (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot ∨
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot := by
  rcases hrigid.2 with hleft | hright
  · exact Or.inl hleft.1
  · exact Or.inr hright.1

end

end HC4.Valuation
