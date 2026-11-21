import HC4.Polynomial.CodimensionTwoTrinomialEulerBridge
import HC4.Polynomial.CodimensionTwoWeightedDepartureClassification
import HC4.Polynomial.CodimensionTwoPrimitiveDepartureKernel
import Mathlib.Tactic

/-!
# Honest singular codimension-two trinomial classification

This is the source-polynomial-facing form of the primitive-departure algebra.
The Euler bridge sends an honest singular trinomial with arbitrary nonzero
coefficients to the coefficient-weighted Hessian-core pencil.  The weighted
classification then forces exactly the three endpoint patterns from the paper
proof.

No valuation state or repair transition enters this file.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Honest singular primitive-departure trinomial classification.** -/
theorem singular_codimensionTwoTrinomial_leftPrimitive_classification
    {D p a c n : ℕ} {C A B : K}
    (hD : 3 ≤ D)
    (hp : 0 < p)
    (hpD : p < D)
    (hn : 0 < n)
    (ha : a + 1 ≤ D)
    (hc : c + n ≤ D)
    (hC : C ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero :
      hessianDeterminant
        (codimensionTwoTrinomial D p a 1 c n C A B) = 0) :
    (n = 1 ∧ a = c) ∨
      (1 < n ∧
        ((a = 0 ∧ p = 1 ∧ c = 0) ∨
          (a = D - 1 ∧ p = D - 1 ∧ c = D - n))) := by
  have hpencil :
      (codimensionTwoWeightedDeparturePencil
        (D : K) (p : K) (a : K) (1 : K)
        (c : K) (n : K) C A B).det = 0 := by
    exact
      det_codimensionTwoWeightedDeparturePencil_eq_zero_of_trinomial_hessian_zero
        (K := K) (D := D) (p := p) (a := a) (m := 1)
        (c := c) (n := n) (C := C) (A := A) (B := B)
        (by omega) hn hzero
  exact
    singular_codimensionTwoWeightedDeparturePencil_leftPrimitive_classification
      (K := K) hD hp hpD hn ha hc hC hA hB hpencil

/-- The two-primitive classified trinomial is literally the standard
constant-kernel pair form. -/
theorem codimensionTwoTrinomial_eq_primitivePairForm
    (D p a : ℕ) (C A B : K) :
    codimensionTwoTrinomial D p a 1 a 1 C A B =
      codimensionTwoPrimitivePairForm D p a C A B := by
  ext d
  simp [codimensionTwoTrinomial, codimensionTwoPrimitivePairForm,
    fourExponentFinsupp, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial]

/-- The lower asymmetric classified trinomial is literally its standard
constant-kernel endpoint form. -/
theorem codimensionTwoTrinomial_eq_lowerEndpointForm
    (D n : ℕ) (C A B : K) (hD : 1 ≤ D) :
    codimensionTwoTrinomial D 1 0 1 0 n C A B =
      codimensionTwoLowerEndpointForm D n C A B := by
  ext d
  simp [codimensionTwoTrinomial, codimensionTwoLowerEndpointForm,
    fourExponentFinsupp, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial, Nat.sub_sub]

/-- The upper asymmetric classified trinomial is literally its standard
constant-kernel endpoint form. -/
theorem codimensionTwoTrinomial_eq_upperEndpointForm
    (D n : ℕ) (C A B : K)
    (hD : 1 ≤ D) (hnD : n ≤ D) :
    codimensionTwoTrinomial D (D - 1) (D - 1) 1 (D - n) n C A B =
      codimensionTwoUpperEndpointForm D n C A B := by
  ext d
  simp [codimensionTwoTrinomial, codimensionTwoUpperEndpointForm,
    fourExponentFinsupp, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial]
  omega

end

end HC4.Polynomial
