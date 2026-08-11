import HC4.Valuation.StrictSmithVisibleFirstContactRigidity
import HC4.Newton.TerminalConformalWeight
import Mathlib.Tactic

/-!
# Constant-residual rigidity in the canonical strict-Smith branch

In the sub-six strict-Smith regime, if the visible first-contact face does
not drop any old special-fibre monomial, then every old special-fibre
monomial has the same positive Smith residual

    smithConformalRawExponent 2 2 d - 4 = m.

Because the raw exponent is twice

    d 1 + d 2 + 2 * d 3,

the positive sub-six residual is forced to be exactly `2` or `4`.
Equivalently, the whole old special fibre is weighted homogeneous for the
transverse weight

    (0,1,1,2)

of weighted degree `3` or `4`.

This file records only that rigid support geometry.  It deliberately does
not introduce a global progress relation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The transverse weight naturally underlying the symmetric Smith
separator. -/
def canonicalSmithTransverseWeight : Fin 4 → ℤ :=
  ![(0 : ℤ), 1, 1, 2]

/-- The `(2,2)` Smith raw exponent is twice the transverse weighted degree. -/
theorem smithConformalRawExponent_two_two_eq_two_mul_transverseDegree
    (d : Fin 4 →₀ ℕ) :
    smithConformalRawExponent 2 2 d =
      2 * (d 1 + d 2 + 2 * d 3) := by
  unfold smithConformalRawExponent
  ring

/-- The custom integral weighted degree for `(0,1,1,2)` is exactly the
transverse quantity `d₁+d₂+2d₃`. -/
theorem integralWeightedDegree_canonicalSmithTransverseWeight
    (d : Fin 4 →₀ ℕ) :
    integralWeightedDegree canonicalSmithTransverseWeight d =
      (d 1 : ℤ) + (d 2 : ℤ) + 2 * (d 3 : ℤ) := by
  unfold integralWeightedDegree canonicalSmithTransverseWeight
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_four, mul_comm]
  · intro i
    simp

/-- The canonical strict-Smith maximal first-contact order is positive. -/
theorem canonicalStrictSmithFirstContactOrder_pos
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0) :
    0 < canonicalStrictSmithFirstContactOrder P hstrict hP := by
  unfold canonicalStrictSmithFirstContactOrder
  exact
    strictSmithCommonParameterOrder_pos
      (canonicalStrictSmithTransformedFamily P hstrict)
      (canonicalStrictSmithTransformedFamily_ne_zero P hstrict hP)
      (canonicalStrictSmithTransformedFamily_commonFactor_one P hstrict)

/-- If every old special-fibre monomial lies on the same sub-six residual,
that residual can only be `2` or `4`. -/
theorem canonicalStrictSmith_constantResidual_order_eq_two_or_four
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hne : (polynomialFamilySpecialFiber P).support.Nonempty)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP) :
    canonicalStrictSmithFirstContactOrder P hstrict hP = 2 ∨
      canonicalStrictSmithFirstContactOrder P hstrict hP = 4 := by
  rcases hne with ⟨d, hd⟩
  have hres := hconst d hd
  have hraw :=
    smithConformalRawExponent_two_two_eq_two_mul_transverseDegree d
  have hpos :=
    canonicalStrictSmithFirstContactOrder_pos
      (K := K) P hstrict hP
  omega

/-- Constant residual `2` means every old special-fibre monomial has
transverse weighted degree `3`. -/
theorem canonicalStrictSmith_constantResidual_two_transverseDegree_three
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP)
    (horder :
      canonicalStrictSmithFirstContactOrder P hstrict hP = 2) :
    ∀ d ∈ (polynomialFamilySpecialFiber P).support,
      d 1 + d 2 + 2 * d 3 = 3 := by
  intro d hd
  have hres := hconst d hd
  have hraw :=
    smithConformalRawExponent_two_two_eq_two_mul_transverseDegree d
  omega

/-- Constant residual `4` means every old special-fibre monomial has
transverse weighted degree `4`. -/
theorem canonicalStrictSmith_constantResidual_four_transverseDegree_four
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP)
    (horder :
      canonicalStrictSmithFirstContactOrder P hstrict hP = 4) :
    ∀ d ∈ (polynomialFamilySpecialFiber P).support,
      d 1 + d 2 + 2 * d 3 = 4 := by
  intro d hd
  have hres := hconst d hd
  have hraw :=
    smithConformalRawExponent_two_two_eq_two_mul_transverseDegree d
  omega

/-- Constant residual `2` packages the old special fibre as weighted
homogeneous of transverse weight `(0,1,1,2)` and degree `3`. -/
theorem canonicalStrictSmith_constantResidual_two_weightedHomogeneous
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP)
    (horder :
      canonicalStrictSmithFirstContactOrder P hstrict hP = 2) :
    IsIntegralWeightedHomogeneous
      canonicalSmithTransverseWeight 3
      (polynomialFamilySpecialFiber P) := by
  intro d hdcoeff
  have hd : d ∈ (polynomialFamilySpecialFiber P).support :=
    MvPolynomial.mem_support_iff.mpr hdcoeff
  have hdeg :=
    canonicalStrictSmith_constantResidual_two_transverseDegree_three
      (K := K) P hstrict hP hconst horder d hd
  rw [integralWeightedDegree_canonicalSmithTransverseWeight]
  exact_mod_cast hdeg

/-- Constant residual `4` packages the old special fibre as weighted
homogeneous of transverse weight `(0,1,1,2)` and degree `4`. -/
theorem canonicalStrictSmith_constantResidual_four_weightedHomogeneous
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP)
    (horder :
      canonicalStrictSmithFirstContactOrder P hstrict hP = 4) :
    IsIntegralWeightedHomogeneous
      canonicalSmithTransverseWeight 4
      (polynomialFamilySpecialFiber P) := by
  intro d hdcoeff
  have hd : d ∈ (polynomialFamilySpecialFiber P).support :=
    MvPolynomial.mem_support_iff.mpr hdcoeff
  have hdeg :=
    canonicalStrictSmith_constantResidual_four_transverseDegree_four
      (K := K) P hstrict hP hconst horder d hd
  rw [integralWeightedDegree_canonicalSmithTransverseWeight]
  exact_mod_cast hdeg

/-- Complete rigid alternative in the constant-residual sub-six branch:
the old special fibre is weighted homogeneous of degree `3` or `4` for
the canonical transverse weight `(0,1,1,2)`. -/
theorem canonicalStrictSmith_constantResidual_weightedDegree_three_or_four
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hne : (polynomialFamilySpecialFiber P).support.Nonempty)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6)
    (hconst :
      ∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP) :
    IsIntegralWeightedHomogeneous
        canonicalSmithTransverseWeight 3
        (polynomialFamilySpecialFiber P) ∨
      IsIntegralWeightedHomogeneous
        canonicalSmithTransverseWeight 4
        (polynomialFamilySpecialFiber P) := by
  rcases
      canonicalStrictSmith_constantResidual_order_eq_two_or_four
        (K := K) P hstrict hP hne hfirst hconst with
    htwo | hfour
  · exact Or.inl
      (canonicalStrictSmith_constantResidual_two_weightedHomogeneous
        (K := K) P hstrict hP hconst htwo)
  · exact Or.inr
      (canonicalStrictSmith_constantResidual_four_weightedHomogeneous
        (K := K) P hstrict hP hconst hfour)

end

end HC4.Valuation
