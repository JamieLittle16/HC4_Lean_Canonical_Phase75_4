import HC4.Valuation.StrictSmithPostTransformFace
import HC4.Valuation.AdaptiveCoefficientOrder
import Mathlib.Tactic

/-!
# Maximal common-parameter normalization for strict Smith improvement

The fixed one-factor strict Smith restart only exposes the parameter-one
layer.  A strict Smith inequality supplies a common factor, but does not say
that this is the *maximal* common factor.  This file records the finite,
coefficientwise normalization which removes the exact least coefficient
valuation instead.

The construction is deliberately independent of any proposed global progress
measure.  It proves only the honest associated-graded facts required before a
Smith-profile comparison can be attempted.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## A generic exact minimum face -/

/-- Removing a common `X^m` factor leaves a coefficient with nonzero
constant term precisely when `m` was that coefficient's exact order. -/
theorem maximalCommonParameter_constantCoeff_ne_zero_iff
    (a m : ℕ) (u v : Polynomial K) (hma : m ≤ a)
    (hu : Polynomial.constantCoeff u ≠ 0)
    (hfactor : Polynomial.X ^ m * v = Polynomial.X ^ a * u) :
    Polynomial.constantCoeff v ≠ 0 ↔ m = a := by
  have hv : v = Polynomial.X ^ (a - m) * u := by
    apply mul_left_cancel₀
      (pow_ne_zero m Polynomial.X_ne_zero)
    calc
      Polynomial.X ^ m * v = Polynomial.X ^ a * u := hfactor
      _ = Polynomial.X ^ m *
          (Polynomial.X ^ (a - m) * u) := by
            rw [← mul_assoc, ← pow_add]
            congr 2
            omega
  rw [hv]
  constructor
  · intro hconst
    by_contra hne
    have hpos : 0 < a - m :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne hma hne)
    apply hconst
    change (Polynomial.X ^ (a - m) * u).coeff 0 = 0
    rw [← Polynomial.X_dvd_iff]
    simpa using
      (dvd_mul_of_dvd_left
        (polynomial_X_pow_dvd_X_pow_of_le
          (K := K) 1 (a - m) hpos) u)
  · intro hEq
    subst a
    simpa using hu

/-- The exact first-contact polynomial obtained from the coefficients of
order `m`.  The primitive parts are proof-independent, so this definition
does not retain support witnesses. -/
noncomputable def maximalCommonParameterFirstContactFace
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ) :
    MvPolynomial (Fin 4) K :=
  ∑ d ∈ P.support.filter
      (fun d => smithFamilyCoefficientOrder P d = m),
    MvPolynomial.monomial d
      (Polynomial.constantCoeff
        (adaptiveSourceCoefficientPrimitivePart P d))

/-- A source monomial survives the special fibre after extracting `X^m`
exactly when its original coefficient has exact order `m`. -/
theorem mem_specialFiber_commonParameterFactor_minOrder_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hmin : ∀ d ∈ P.support, m ≤ smithFamilyCoefficientOrder P d)
    (hdiv : HasCommonParameterFactor m P)
    (d : Fin 4 →₀ ℕ) :
    d ∈ (polynomialFamilySpecialFiber
        (commonParameterFactorFamily m P hdiv)).support ↔
      d ∈ P.support ∧ smithFamilyCoefficientOrder P d = m := by
  by_cases hd : d ∈ P.support
  · have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    let a := smithFamilyCoefficientOrder P d
    let u := polynomialParameterPrimitivePart
      (MvPolynomial.coeff d P) hcoeff
    let v := MvPolynomial.coeff d
      (commonParameterFactorFamily m P hdiv)
    have ha : a = polynomialParameterOrder
        (MvPolynomial.coeff d P) hcoeff := by
      simp [a, smithFamilyCoefficientOrder, hd,
        smithFamilyCoefficientParameterOrder]
    have hprimitive : MvPolynomial.coeff d P =
        Polynomial.X ^ a * u := by
      rw [ha]
      exact polynomialParameterPrimitivePart_spec _ hcoeff
    have hquotient : Polynomial.X ^ m * v =
        MvPolynomial.coeff d P := by
      exact (commonParameterFactorFamily_coeff_factorisation m P hdiv d).symm
    have hu : Polynomial.constantCoeff u ≠ 0 := by
      exact polynomialParameterPrimitivePart_constantCoeff_ne_zero _ hcoeff
    have hconst : Polynomial.constantCoeff v ≠ 0 ↔ m = a := by
      apply maximalCommonParameter_constantCoeff_ne_zero_iff
        (a := a) (m := m) (u := u) (v := v)
        (hmin d hd) hu
      exact hquotient.trans hprimitive
    rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber]
    simpa [v, a, hd, eq_comm] using hconst
  · rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber,
      coeff_commonParameterFactorFamily_of_not_mem m P hdiv hd]
    simp [hd]

/-- Coefficient form of the exact first-contact face. -/
theorem coeff_specialFiber_commonParameterFactor_minOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hmin : ∀ d ∈ P.support, m ≤ smithFamilyCoefficientOrder P d)
    (hdiv : HasCommonParameterFactor m P)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (polynomialFamilySpecialFiber
          (commonParameterFactorFamily m P hdiv)) =
      if hd : d ∈ P.support ∧ smithFamilyCoefficientOrder P d = m then
        Polynomial.constantCoeff
          (adaptiveSourceCoefficientPrimitivePart P d)
      else 0 := by
  by_cases hd : d ∈ P.support
  · have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    let a := smithFamilyCoefficientOrder P d
    let primitive := polynomialParameterPrimitivePart
      (MvPolynomial.coeff d P) hcoeff
    let quotient := MvPolynomial.coeff d
      (commonParameterFactorFamily m P hdiv)
    have ha : a = polynomialParameterOrder
        (MvPolynomial.coeff d P) hcoeff := by
      simp [a, smithFamilyCoefficientOrder, hd,
        smithFamilyCoefficientParameterOrder]
    have hprimitive : MvPolynomial.coeff d P =
        Polynomial.X ^ a * primitive := by
      rw [ha]
      exact polynomialParameterPrimitivePart_spec _ hcoeff
    have hquotient : Polynomial.X ^ m * quotient =
        MvPolynomial.coeff d P := by
      exact (commonParameterFactorFamily_coeff_factorisation m P hdiv d).symm
    have hprimitiveConst : Polynomial.constantCoeff primitive ≠ 0 := by
      exact polynomialParameterPrimitivePart_constantCoeff_ne_zero _ hcoeff
    have hadapt : adaptiveSourceCoefficientPrimitivePart P d = primitive := by
      simp [adaptiveSourceCoefficientPrimitivePart, hcoeff, primitive]
    by_cases horder : smithFamilyCoefficientOrder P d = m
    · have horder' : a = m := by
        simpa [a] using horder
      have hq : quotient = primitive := by
        apply mul_left_cancel₀
          (pow_ne_zero m Polynomial.X_ne_zero)
        calc
          Polynomial.X ^ m * quotient = MvPolynomial.coeff d P := hquotient
          _ = Polynomial.X ^ a * primitive := hprimitive
          _ = Polynomial.X ^ m * primitive := by
            rw [horder']
      rw [coeff_polynomialFamilySpecialFiber]
      simp only [quotient] at hq
      rw [hq, hadapt]
      simp [hd, horder]
    · have hconst : Polynomial.constantCoeff quotient = 0 := by
        by_contra hne
        have hEq : m = a :=
          (maximalCommonParameter_constantCoeff_ne_zero_iff
            (a := a) (m := m) (u := primitive) (v := quotient)
            (hmin d hd) hprimitiveConst
            (hquotient.trans hprimitive)).mp hne
        exact horder (by simpa [a] using hEq.symm)
      rw [coeff_polynomialFamilySpecialFiber]
      simp only [quotient] at hconst
      rw [hconst]
      simp [hd, horder]
  · rw [coeff_polynomialFamilySpecialFiber,
      coeff_commonParameterFactorFamily_of_not_mem m P hdiv hd]
    simp [hd]

/-- Exact polynomial form of maximal common-parameter normalization. -/
theorem polynomialFamilySpecialFiber_commonParameterFactor_minOrder_eq_face
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hmin : ∀ d ∈ P.support, m ≤ smithFamilyCoefficientOrder P d)
    (hdiv : HasCommonParameterFactor m P) :
    polynomialFamilySpecialFiber
        (commonParameterFactorFamily m P hdiv) =
      maximalCommonParameterFirstContactFace P m := by
  ext d
  rw [coeff_specialFiber_commonParameterFactor_minOrder
    (K := K) P m hmin hdiv]
  classical
  by_cases hd : d ∈ P.support
  · by_cases hm : smithFamilyCoefficientOrder P d = m
    · simp [maximalCommonParameterFirstContactFace, hd, hm,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    · simp [maximalCommonParameterFirstContactFace, hd, hm,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  · simp [maximalCommonParameterFirstContactFace, hd,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

/-- Attainment of the exact minimum makes the maximally normalized special
fibre nonzero. -/
theorem polynomialFamilySpecialFiber_commonParameterFactor_minOrder_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (m : ℕ)
    (hmin : ∀ d ∈ P.support, m ≤ smithFamilyCoefficientOrder P d)
    (hdiv : HasCommonParameterFactor m P)
    (hattain : ∃ d ∈ P.support,
      smithFamilyCoefficientOrder P d = m) :
    polynomialFamilySpecialFiber
        (commonParameterFactorFamily m P hdiv) ≠ 0 := by
  rcases hattain with ⟨d, hd, hm⟩
  intro hzero
  have hmem : d ∈ (polynomialFamilySpecialFiber
      (commonParameterFactorFamily m P hdiv)).support :=
    (mem_specialFiber_commonParameterFactor_minOrder_iff
      (K := K) P m hmin hdiv d).mpr ⟨hd, hm⟩
  rw [hzero] at hmem
  simpa using hmem

/-! ## Strict Smith instantiation -/

/-- A nonzero family with one common parameter factor has a positive
coefficient-order minimum. -/
theorem strictSmith_hasPositiveParameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    HasPositiveParameterLayer P := by
  rcases MvPolynomial.support_nonempty.mpr hP with ⟨d, hd⟩
  refine ⟨smithFamilyCoefficientOrder P d, ?_⟩
  rw [familyPositiveParameterOrders]
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
  rw [smithFamilyCoefficientOrder_eq P hd]
  exact polynomial_X_pow_dvd_le_parameterOrder
    (MvPolynomial.coeff d P)
    (MvPolynomial.mem_support_iff.mp hd) 1
    (by simpa using hcommon d hd)

/-- The exact maximal common parameter order in the strict Smith branch. -/
noncomputable def strictSmithCommonParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) : ℕ :=
  firstPositiveParameterOrder P
    (strictSmith_hasPositiveParameterLayer P hP hcommon)

theorem strictSmithCommonParameterOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    0 < strictSmithCommonParameterOrder P hP hcommon := by
  exact firstPositiveParameterOrder_pos P
    (strictSmith_hasPositiveParameterLayer P hP hcommon)

theorem strictSmithCommonParameterOrder_le
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    strictSmithCommonParameterOrder P hP hcommon ≤
      smithFamilyCoefficientOrder P d := by
  apply firstPositiveParameterOrder_le P
    (strictSmith_hasPositiveParameterLayer P hP hcommon) hd
  rw [smithFamilyCoefficientOrder_eq P hd]
  exact polynomial_X_pow_dvd_le_parameterOrder
    (MvPolynomial.coeff d P)
    (MvPolynomial.mem_support_iff.mp hd) 1
    (by simpa using hcommon d hd)

theorem strictSmithCommonParameterOrder_realised
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    ∃ d ∈ P.support,
      smithFamilyCoefficientOrder P d =
        strictSmithCommonParameterOrder P hP hcommon := by
  exact firstPositiveParameterOrder_realised P
    (strictSmith_hasPositiveParameterLayer P hP hcommon)

/-- Every source coefficient is divisible by the maximal common strict Smith
parameter factor. -/
theorem strictSmith_maximalCommonParameterFactor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    HasCommonParameterFactor
      (strictSmithCommonParameterOrder P hP hcommon) P := by
  intro d hd
  have hle := strictSmithCommonParameterOrder_le P hP hcommon hd
  exact dvd_trans
    (polynomial_X_pow_dvd_X_pow_of_le (K := K)
      _ _ hle)
    (smithFamilyCoefficientOrder_dvd P hd)

/-- The coefficientwise maximally normalized strict Smith family. -/
noncomputable def maximallyNormalizedStrictSmithFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  commonParameterFactorFamily
    (strictSmithCommonParameterOrder P hP hcommon) P
    (strictSmith_maximalCommonParameterFactor P hP hcommon)

/-- The maximally normalized strict Smith family exposes precisely its
attained coefficient-order face. -/
theorem specialFiber_maximallyNormalizedStrictSmith_eq_firstContactFace
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    polynomialFamilySpecialFiber
        (maximallyNormalizedStrictSmithFamily P hP hcommon) =
      maximalCommonParameterFirstContactFace P
        (strictSmithCommonParameterOrder P hP hcommon) := by
  unfold maximallyNormalizedStrictSmithFamily
  exact polynomialFamilySpecialFiber_commonParameterFactor_minOrder_eq_face
    (K := K) P _
    (fun d hd => strictSmithCommonParameterOrder_le P hP hcommon hd)
    (strictSmith_maximalCommonParameterFactor P hP hcommon)

/-- Maximal strict Smith normalization always has a nonzero special fibre. -/
theorem specialFiber_maximallyNormalizedStrictSmith_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P) :
    polynomialFamilySpecialFiber
        (maximallyNormalizedStrictSmithFamily P hP hcommon) ≠ 0 := by
  unfold maximallyNormalizedStrictSmithFamily
  exact polynomialFamilySpecialFiber_commonParameterFactor_minOrder_ne_zero
    (K := K) P _
    (fun d hd => strictSmithCommonParameterOrder_le P hP hcommon hd)
    (strictSmith_maximalCommonParameterFactor P hP hcommon)
    (strictSmithCommonParameterOrder_realised P hP hcommon)

theorem mem_specialFiber_maximallyNormalizedStrictSmith_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hP : P ≠ 0)
    (hcommon : HasCommonParameterFactor 1 P)
    (d : Fin 4 →₀ ℕ) :
    d ∈ (polynomialFamilySpecialFiber
        (maximallyNormalizedStrictSmithFamily P hP hcommon)).support ↔
      d ∈ P.support ∧
        smithFamilyCoefficientOrder P d =
          strictSmithCommonParameterOrder P hP hcommon := by
  unfold maximallyNormalizedStrictSmithFamily
  exact mem_specialFiber_commonParameterFactor_minOrder_iff
    (K := K) P _
    (fun d hd => strictSmithCommonParameterOrder_le P hP hcommon hd)
    (strictSmith_maximalCommonParameterFactor P hP hcommon) d

end

end HC4.Valuation
