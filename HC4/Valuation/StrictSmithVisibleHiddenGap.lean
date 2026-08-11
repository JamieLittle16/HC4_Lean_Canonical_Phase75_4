import HC4.Valuation.StrictSmithFirstContactGeometry
import HC4.Valuation.BinarySmithOrderExtraction
import HC4.Valuation.AlignedSmithFirstStop
import Mathlib.Tactic

/-!
# Canonical strict-Smith visible/hidden first-contact gap

The exact strict-Smith coefficient-order formula is now available.  This
file specialises it to the canonical binary Smith base.

For a supported source coefficient there are two cases.

* exact source order `0`: the binary Smith base is `0`, strictness forces
  the symmetric separator to be positive, and the transformed exact order
  is the visible Smith residual `raw(d) - 4`;

* positive source order: the ramification-by-ten contribution already
  contributes at least `10`, so after the conformal `X^4` normalisation
  the transformed exact order is at least `6`.

This is deliberately only a first-contact separation theorem.  It does not
define or assume any global progress measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Exact source order zero forces the canonical binary Smith base of the
projected class to be zero. -/
theorem smithBinaryBase_eq_zero_of_exactOrder_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (horder : smithFamilyCoefficientOrder P d = 0) :
    smithBinaryBase P (smithAxisProjection d) = 0 := by
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdiv :=
    smithBinaryBase_coefficientOrderLowerBound P d hd
  have hle :
      smithBinaryBase P (smithAxisProjection d) ≤
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne :=
    polynomial_X_pow_dvd_le_parameterOrder
      (MvPolynomial.coeff d P) hcoeffne
      (smithBinaryBase P (smithAxisProjection d))
      hdiv
  have hexact :
      smithFamilyCoefficientOrder P d =
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
    rw [smithFamilyCoefficientOrder_eq P hd]
    rfl
  omega

/-- A positive exact source order leaves at least six parameter powers after
the ramification-by-ten strict Smith transform and the conformal `X^4`
normalisation. -/
theorem strictSmithResidualExponent_ge_six_of_sourceOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (horder : 0 < smithFamilyCoefficientOrder P d) :
    6 ≤ strictSmithResidualExponent P d := by
  unfold strictSmithResidualExponent
  omega

/-- On an exact-order-zero source monomial, canonical strict improvement
forces the symmetric Smith separator to be strictly positive. -/
theorem canonicalStrictSmith_separatorDelta_pos_of_sourceOrder_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (horder : smithFamilyCoefficientOrder P d = 0) :
    0 < smithSeparatorDelta 1 1 (smithAxisProjection d) := by
  have hbase0 :=
    smithBinaryBase_eq_zero_of_exactOrder_zero P hd horder
  have hraw :=
    strictSymmetricImprovement_raw_plus_base_ge_five
      (K := K) (smithBinaryBase P) P hstrict hd
  have hraw5 :
      5 ≤ smithConformalRawExponent 2 2 d := by
    simpa [hbase0] using hraw
  rw [smithSeparatorDelta_projection_eq_raw_sub_four]
  have hraw5z :
      (5 : ℤ) ≤ (smithConformalRawExponent 2 2 d : ℤ) := by
    exact_mod_cast hraw5
  omega

/-- On an exact-order-zero source monomial, the transformed exact parameter
order is precisely the visible Smith residual `raw(d) - 4`. -/
theorem canonicalStrictSmith_transformedOrder_eq_raw_sub_four_of_sourceOrder_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (horder : smithFamilyCoefficientOrder P d = 0) :
    smithFamilyCoefficientOrder
        (strictSymmetricSmithTransformedFamily
          (smithBinaryBase P) P
          (smithBinaryBase_coefficientOrderLowerBound P)
          hstrict)
        d =
      smithConformalRawExponent 2 2 d - 4 := by
  calc
    smithFamilyCoefficientOrder
        (strictSymmetricSmithTransformedFamily
          (smithBinaryBase P) P
          (smithBinaryBase_coefficientOrderLowerBound P)
          hstrict)
        d =
      strictSmithResidualExponent P d :=
        strictSymmetricImprovement_transformedCoefficientOrder_eq_residual
          (K := K)
          (smithBinaryBase P) P
          (smithBinaryBase_coefficientOrderLowerBound P)
          hstrict hd
    _ = smithConformalRawExponent 2 2 d - 4 := by
      simp [strictSmithResidualExponent, horder]

/-- A genuinely hidden positive-order source monomial has transformed exact
parameter order at least six. -/
theorem canonicalStrictSmith_transformedOrder_ge_six_of_sourceOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support)
    (horder : 0 < smithFamilyCoefficientOrder P d) :
    6 ≤
      smithFamilyCoefficientOrder
        (strictSymmetricSmithTransformedFamily
          (smithBinaryBase P) P
          (smithBinaryBase_coefficientOrderLowerBound P)
          hstrict)
        d := by
  rw [
    strictSymmetricImprovement_transformedCoefficientOrder_eq_residual
      (K := K)
      (smithBinaryBase P) P
      (smithBinaryBase_coefficientOrderLowerBound P)
      hstrict hd]
  exact strictSmithResidualExponent_ge_six_of_sourceOrder_pos P d horder

/-- Canonical strict-Smith source coefficients split exactly into a visible
order-zero branch with positive Smith separator and a hidden branch whose
transformed exact order is at least six. -/
theorem canonicalStrictSmith_transformedOrder_visible_or_hidden
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    (smithFamilyCoefficientOrder P d = 0 ∧
        0 < smithSeparatorDelta 1 1 (smithAxisProjection d) ∧
        smithFamilyCoefficientOrder
            (strictSymmetricSmithTransformedFamily
              (smithBinaryBase P) P
              (smithBinaryBase_coefficientOrderLowerBound P)
              hstrict)
            d =
          smithConformalRawExponent 2 2 d - 4) ∨
      (0 < smithFamilyCoefficientOrder P d ∧
        6 ≤
          smithFamilyCoefficientOrder
            (strictSymmetricSmithTransformedFamily
              (smithBinaryBase P) P
              (smithBinaryBase_coefficientOrderLowerBound P)
              hstrict)
            d) := by
  by_cases hzero : smithFamilyCoefficientOrder P d = 0
  · left
    refine ⟨hzero, ?_, ?_⟩
    · exact
        canonicalStrictSmith_separatorDelta_pos_of_sourceOrder_zero
          (K := K) P hstrict hd hzero
    · exact
        canonicalStrictSmith_transformedOrder_eq_raw_sub_four_of_sourceOrder_zero
          (K := K) P hstrict hd hzero
  · right
    have hpos : 0 < smithFamilyCoefficientOrder P d :=
      Nat.pos_of_ne_zero hzero
    exact
      ⟨hpos,
        canonicalStrictSmith_transformedOrder_ge_six_of_sourceOrder_pos
          (K := K) P hstrict hd hpos⟩

end

end HC4.Valuation
