import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.BinarySmithOrderExtraction
import HC4.Valuation.AdaptiveCoefficientOrder
import HC4.Valuation.AdaptiveDegreeTwoSaturatedFace

/-!
# Exact first post-transform face of strict symmetric Smith improvement

Strict symmetric Smith improvement proves that the conformally transformed
family has a common parameter factor.  Removing that one factor does not,
by itself, prove that the resulting special fibre is nonzero: the incoming
coefficients may have had more parameter order than the binary lower bound.

This file records the exact statement available without an additional
attainment hypothesis.  The new special fibre is precisely the *first
parameter coefficient layer* of the pre-extraction Smith family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Coefficient form of common-factor extraction: the special coefficient
of the quotient is the parameter-one coefficient before extraction. -/
theorem coeff_polynomialFamilySpecialFiber_commonParameterFactor_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          (commonParameterFactorFamily 1 P hdiv)) =
      (MvPolynomial.coeff d P).coeff 1 := by
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.coeff_map]
  have hfactor :=
    commonParameterFactorFamily_coeff_factorisation 1 P hdiv d
  have hcoeff_one := congrArg (fun c : Polynomial K => c.coeff 1) hfactor
  simpa using hcoeff_one.symm

/-- Removing one common parameter factor converts the parameter-one layer
of the original family exactly into the special fibre of the quotient. -/
theorem polynomialFamilySpecialFiber_commonParameterFactor_one_eq_layer_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P) :
    polynomialFamilySpecialFiber
      (commonParameterFactorFamily 1 P hdiv) =
      familyParameterLayer P 1 := by
  ext d
  rw [familyParameterLayer_coeff]
  exact coeff_polynomialFamilySpecialFiber_commonParameterFactor_one
    (K := K) P hdiv d

/-- Support form of the same exact first-layer identity. -/
theorem mem_specialFiber_commonParameterFactor_one_support_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P)
    (d : Fin 4 →₀ ℕ) :
    d ∈ (polynomialFamilySpecialFiber
        (commonParameterFactorFamily 1 P hdiv)).support ↔
      (MvPolynomial.coeff d P).coeff 1 ≠ 0 := by
  rw [MvPolynomial.mem_support_iff,
    coeff_polynomialFamilySpecialFiber_commonParameterFactor_one]

/-- The strict symmetric Smith branch has an exact post-transform face:
it is the parameter-one coefficient potential of the integral Smith family.
This is the strongest conclusion available from strict improvement and the
binary coefficient-order lower bound alone. -/
theorem strictSymmetricImprovement_postSpecialFiber_eq_layer_one
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HC4.Newton.HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P) 0
        (fun e => (base e : ℤ))) :
    let Pram := parameterRamificationFamily (K := K) 10 P
    let hsmith := strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base P hbase hstrict
    let Psmith := integralSmithConformalFamily 2 2 Pram hsmith
    let hcommon := strictSymmetricImprovement_commonParameterFactor
      (K := K) base P hbase hstrict hsmith
    polynomialFamilySpecialFiber
      (commonParameterFactorFamily 1 Psmith hcommon) =
      familyParameterLayer Psmith 1 := by
  dsimp
  exact polynomialFamilySpecialFiber_commonParameterFactor_one_eq_layer_one
    (K := K) _ _

/-- Strict improvement alone supplies no attainment statement for the
parameter-one layer.  Thus callers which need a nonzero post-transform
special fibre must additionally provide a first-level attainment certificate
or extract the maximal common parameter factor. -/
def HasStrictSmithFirstLayerAttainment
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  familyParameterLayer P 1 ≠ 0

/-- The exact additional datum needed to ensure the one-factor strict Smith
quotient has a nonzero special fibre. -/
theorem polynomialFamilySpecialFiber_commonParameterFactor_one_ne_zero_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P) :
    polynomialFamilySpecialFiber
        (commonParameterFactorFamily 1 P hdiv) ≠ 0 ↔
      HasStrictSmithFirstLayerAttainment P := by
  rw [polynomialFamilySpecialFiber_commonParameterFactor_one_eq_layer_one]
  rfl

/-! ## Maximal common parameter normalisation -/

/-- The least exact parameter order among the nonzero source coefficients of
`P`.  This is the largest common `X`-power that can be removed from `P`
coefficientwise. -/
noncomputable def minimalAdaptiveFamilyParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty) : ℕ :=
  (P.support.image (adaptiveSourceCoefficientParameterOrder P)).min'
    (hne.image _)

/-- The selected minimum is realised by an actual source exponent. -/
theorem minimalAdaptiveFamilyParameterOrder_mem_image
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty) :
    minimalAdaptiveFamilyParameterOrder P hne ∈
      P.support.image (adaptiveSourceCoefficientParameterOrder P) := by
  unfold minimalAdaptiveFamilyParameterOrder
  exact Finset.min'_mem _ (hne.image _)

/-- An actual source coefficient attains the common parameter order. -/
theorem exists_sourceCoefficient_minimalAdaptiveFamilyParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty) :
    ∃ d ∈ P.support,
      adaptiveSourceCoefficientParameterOrder P d =
        minimalAdaptiveFamilyParameterOrder P hne := by
  have hmem := minimalAdaptiveFamilyParameterOrder_mem_image P hne
  rcases Finset.mem_image.mp hmem with ⟨d, hd, heq⟩
  exact ⟨d, hd, heq⟩

/-- The common parameter order is a lower bound for every nonzero source
coefficient order. -/
theorem minimalAdaptiveFamilyParameterOrder_le
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    minimalAdaptiveFamilyParameterOrder P hne ≤
      adaptiveSourceCoefficientParameterOrder P d := by
  unfold minimalAdaptiveFamilyParameterOrder
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨d, hd, rfl⟩)

/-- Exact coefficient orders make the finite minimum an honest common
parameter factor of the whole family. -/
theorem minimalAdaptiveFamilyParameterOrder_commonFactor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty) :
    HasCommonParameterFactor
      (minimalAdaptiveFamilyParameterOrder P hne) P := by
  intro d hd
  have hle := minimalAdaptiveFamilyParameterOrder_le P hne hd
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have horder :
      Polynomial.X ^ adaptiveSourceCoefficientParameterOrder P d ∣
        MvPolynomial.coeff d P := by
    simpa [adaptiveSourceCoefficientParameterOrder, hcoeffne] using
      polynomialParameterOrder_dvd (MvPolynomial.coeff d P) hcoeffne
  exact dvd_trans
    (polynomial_X_pow_dvd_X_pow_of_le
      (K := K) _ _ hle)
    horder

/-- After removing the maximal common factor, the special fibre consists
exactly of source coefficients whose exact order attained the finite
minimum. -/
theorem mem_specialFiber_maximalCommonParameterFactor_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty)
    (d : Fin 4 →₀ ℕ) :
    let m := minimalAdaptiveFamilyParameterOrder P hne
    let hdiv := minimalAdaptiveFamilyParameterOrder_commonFactor P hne
    d ∈ (polynomialFamilySpecialFiber
      (commonParameterFactorFamily m P hdiv)).support ↔
      d ∈ P.support ∧
        adaptiveSourceCoefficientParameterOrder P d = m := by
  dsimp only
  let m := minimalAdaptiveFamilyParameterOrder P hne
  let hdiv := minimalAdaptiveFamilyParameterOrder_commonFactor P hne
  by_cases hd : d ∈ P.support
  · have hle : m ≤ adaptiveSourceCoefficientParameterOrder P d := by
      exact minimalAdaptiveFamilyParameterOrder_le P hne hd
    have hprimitive : Polynomial.constantCoeff
        (adaptiveSourceCoefficientPrimitivePart P d) ≠ 0 :=
      adaptiveSourceCoefficientPrimitivePart_constantCoeff_ne_zero P hd
    have hfactor :
        Polynomial.X ^ m *
          MvPolynomial.coeff d (commonParameterFactorFamily m P hdiv) =
        Polynomial.X ^ adaptiveSourceCoefficientParameterOrder P d *
          adaptiveSourceCoefficientPrimitivePart P d := by
      rw [← commonParameterFactorFamily_coeff_factorisation]
      exact adaptiveSourceCoefficient_exactFactorization P hd
    have hconstant : Polynomial.constantCoeff
        (MvPolynomial.coeff d (commonParameterFactorFamily m P hdiv)) ≠ 0 ↔
        m = adaptiveSourceCoefficientParameterOrder P d := by
      exact constantCoeff_ne_zero_of_exact_X_power_quotient_iff
        (a := adaptiveSourceCoefficientParameterOrder P d) (b := m)
        (u := adaptiveSourceCoefficientPrimitivePart P d)
        (v := MvPolynomial.coeff d (commonParameterFactorFamily m P hdiv))
        hle hprimitive hfactor
    rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber]
    simpa [hd, eq_comm] using hconstant
  · have hquot :
      MvPolynomial.coeff d (commonParameterFactorFamily m P hdiv) = 0 :=
      coeff_commonParameterFactorFamily_of_not_mem m P hdiv hd
    rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber,
      hquot]
    simp [hd]

/-- Maximal common-factor normalisation has a nonzero special fibre: a
finite minimum is attained, and its primitive coefficient survives. -/
theorem polynomialFamilySpecialFiber_maximalCommonParameterFactor_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hne : P.support.Nonempty) :
    let m := minimalAdaptiveFamilyParameterOrder P hne
    let hdiv := minimalAdaptiveFamilyParameterOrder_commonFactor P hne
    polynomialFamilySpecialFiber
      (commonParameterFactorFamily m P hdiv) ≠ 0 := by
  dsimp only
  obtain ⟨d, hd, hmin⟩ :=
    exists_sourceCoefficient_minimalAdaptiveFamilyParameterOrder P hne
  have hmem : d ∈ (polynomialFamilySpecialFiber
      (commonParameterFactorFamily
        (minimalAdaptiveFamilyParameterOrder P hne) P
        (minimalAdaptiveFamilyParameterOrder_commonFactor P hne))).support := by
    have hiff := mem_specialFiber_maximalCommonParameterFactor_iff P hne d
    dsimp only at hiff
    exact hiff.mpr ⟨hd, hmin⟩
  intro hzero
  rw [hzero] at hmem
  simpa using hmem

/-- Strict symmetric Smith improvement forces the maximal common parameter
order of the integral Smith family to be positive.  It does *not* force that
order to equal one; maximal normalisation is therefore the honest way to
obtain a nonzero post-transform special fibre. -/
theorem strictSymmetricImprovement_minimalParameterOrder_pos
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HC4.Newton.HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P) 0
        (fun e => (base e : ℤ)))
    (hne :
      (integralSmithConformalFamily 2 2
        (parameterRamificationFamily (K := K) 10 P)
        (strictSymmetricImprovement_integralSmithDivisibility
          (K := K) base P hbase hstrict)).support.Nonempty) :
    1 ≤ minimalAdaptiveFamilyParameterOrder
      (integralSmithConformalFamily 2 2
        (parameterRamificationFamily (K := K) 10 P)
        (strictSymmetricImprovement_integralSmithDivisibility
          (K := K) base P hbase hstrict)) hne := by
  let Pram := parameterRamificationFamily (K := K) 10 P
  let hsmith := strictSymmetricImprovement_integralSmithDivisibility
    (K := K) base P hbase hstrict
  let Psmith := integralSmithConformalFamily 2 2 Pram hsmith
  let hcommon := strictSymmetricImprovement_commonParameterFactor
    (K := K) base P hbase hstrict hsmith
  obtain ⟨d, hd, hmin⟩ :=
    exists_sourceCoefficient_minimalAdaptiveFamilyParameterOrder Psmith hne
  have hcoeffne : MvPolynomial.coeff d Psmith ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have horder : 1 ≤ adaptiveSourceCoefficientParameterOrder Psmith d := by
    have hdiv := hcommon d hd
    simpa [adaptiveSourceCoefficientParameterOrder, hcoeffne] using
      polynomial_X_pow_dvd_le_parameterOrder
        (MvPolynomial.coeff d Psmith) hcoeffne 1 hdiv
  rw [← hmin]
  exact horder

end

end HC4.Valuation
