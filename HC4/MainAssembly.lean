import HC4.ClassifiedFamilies.PolynomialEndpoint
import HC4.Toric.ClassifiedDescent

/-!
# Final automorphism assembly

The hard geometric part of the paper produces one of the two polynomial
classification witnesses.  This module records the exact final implication:
once a gradient map is identified with either displayed classified formula,
it is a polynomial bijection with the verified explicit inverse.
-/

namespace HC4

open ClassifiedFamilies

section CommRing

variable {K : Type*} [CommRing K]

/-- A function has one of the two classified polynomial gradient formulae. -/
def HasClassifiedPolynomialGradient
    (a b : ℕ) (G : Point4 K → Point4 K) : Prop :=
  ∃ B : PolynomialBranch K, G = polynomialBranchGradient a b B

/-- The classified formula immediately implies bijectivity. -/
theorem gradient_bijective_of_classified_polynomial
    (a b : ℕ) {G : Point4 K → Point4 K}
    (hG : HasClassifiedPolynomialGradient a b G) :
    Function.Bijective G := by
  rcases hG with ⟨B, rfl⟩
  exact polynomialBranchGradient_bijective a b B

/-- The classified formula supplies a concrete two-sided inverse. -/
theorem exists_two_sided_inverse_of_classified_polynomial
    (a b : ℕ) {G : Point4 K → Point4 K}
    (hG : HasClassifiedPolynomialGradient a b G) :
    ∃ Ginv : Point4 K → Point4 K,
      Function.LeftInverse Ginv G ∧ Function.RightInverse Ginv G := by
  rcases hG with ⟨B, rfl⟩
  exact ⟨polynomialBranchInverse a b B,
    polynomialBranchInverse_comp_gradient a b B,
    polynomialBranchGradient_comp_inverse a b B⟩

/-- The final endpoint packaged as an affine-space equivalence. -/
noncomputable def gradientEquivOfClassifiedPolynomial
    (a b : ℕ) (G : Point4 K → Point4 K)
    (hG : HasClassifiedPolynomialGradient a b G) : Point4 K ≃ Point4 K := by
  classical
  let B : PolynomialBranch K := Classical.choose hG
  have hB : G = polynomialBranchGradient a b B := Classical.choose_spec hG
  exact
    { toFun := G
      invFun := polynomialBranchInverse a b B
      left_inv := by
        intro x
        rw [hB]
        exact polynomialBranchInverse_comp_gradient a b B x
      right_inv := by
        intro x
        rw [hB]
        exact polynomialBranchGradient_comp_inverse a b B x }

end CommRing

end HC4
