import HC4.Polynomial.WeightedInitial
import HC4.Toric.Facets

/-!
# Four-variable monomial exponents and toric support

This module connects the genuine `MvPolynomial (Fin 4)` monomial exponent
representation to the `HC4.Toric.Exponent` representation used by the
symmetric-grading semigroup development.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

/-- Convert an `MvPolynomial (Fin 4)` monomial exponent to the toric four-tuple. -/
def toToricExponent (d : Fin 4 →₀ ℕ) : HC4.Toric.Exponent :=
  ⟨d 0, d 1, d 2, d 3⟩

/-- Ordinary total degree of a four-variable monomial exponent. -/
def ordinaryDegree4 (d : Fin 4 →₀ ℕ) : ℕ :=
  d 0 + d 1 + d 2 + d 3

@[simp] theorem toToricExponent_x1 (d : Fin 4 →₀ ℕ) :
    (toToricExponent d).x1 = d 0 := rfl
@[simp] theorem toToricExponent_x2 (d : Fin 4 →₀ ℕ) :
    (toToricExponent d).x2 = d 1 := rfl
@[simp] theorem toToricExponent_x3 (d : Fin 4 →₀ ℕ) :
    (toToricExponent d).x3 = d 2 := rfl
@[simp] theorem toToricExponent_x4 (d : Fin 4 →₀ ℕ) :
    (toToricExponent d).x4 = d 3 := rfl

/-- The symmetric torus balance equation on a genuine MvPolynomial exponent. -/
def IsBalancedExponent (a b : ℕ) (d : Fin 4 →₀ ℕ) : Prop :=
  a * d 0 + b * d 1 = b * d 2 + a * d 3

@[simp] theorem isBalancedExponent_iff_balanced (a b : ℕ) (d : Fin 4 →₀ ℕ) :
    IsBalancedExponent a b d ↔ HC4.Toric.Balanced a b (toToricExponent d) := by
  rfl


/-- The coordinate omitted by a toric facet. -/
def facetOmittedCoordinate : HC4.Toric.ToricFacet → Fin 4
  | .pr => 1
  | .rq => 3
  | .qs => 0
  | .sp => 2

/-- Facet membership is exactly vanishing of the omitted coordinate. -/
@[simp] theorem onFacet_toToricExponent_iff
    (F : HC4.Toric.ToricFacet) (d : Fin 4 →₀ ℕ) :
    HC4.Toric.OnFacet F (toToricExponent d) ↔ d (facetOmittedCoordinate F) = 0 := by
  cases F <;> rfl

/-- A positive omitted coordinate witnesses failure of facet membership. -/
theorem not_onFacet_toToricExponent_of_pos
    {F : HC4.Toric.ToricFacet} {d : Fin 4 →₀ ℕ}
    (hpos : 0 < d (facetOmittedCoordinate F)) :
    ¬ HC4.Toric.OnFacet F (toToricExponent d) := by
  rw [onFacet_toToricExponent_iff]
  omega

/-- Every supported monomial of an actual four-variable polynomial is torus invariant. -/
def HasBalancedMvSupport {K : Type*} [CommSemiring K]
    (a b : ℕ) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ p.support, IsBalancedExponent a b d

/-- Actual polynomial support lies in one chosen toric facet. -/
def MvSupportOnFacet {K : Type*} [CommSemiring K]
    (F : HC4.Toric.ToricFacet) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ p.support, HC4.Toric.OnFacet F (toToricExponent d)

/-- A monomial is on the boundary of the invariant cone when it omits a coordinate. -/
def MvExponentOnBoundary (d : Fin 4 →₀ ℕ) : Prop :=
  ∃ F : HC4.Toric.ToricFacet, HC4.Toric.OnFacet F (toToricExponent d)

/-- In four variables, cone-boundary membership is exactly omission of at
least one coordinate. -/
theorem mvExponentOnBoundary_iff_coordinate_zero (d : Fin 4 →₀ ℕ) :
    MvExponentOnBoundary d ↔ d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0 ∨ d 3 = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    cases F with
    | pr => exact Or.inr (Or.inl ((onFacet_toToricExponent_iff .pr d).1 hF))
    | rq => exact Or.inr (Or.inr (Or.inr ((onFacet_toToricExponent_iff .rq d).1 hF)))
    | qs => exact Or.inl ((onFacet_toToricExponent_iff .qs d).1 hF)
    | sp => exact Or.inr (Or.inr (Or.inl ((onFacet_toToricExponent_iff .sp d).1 hF)))
  · intro h
    rcases h with h0 | h1 | h2 | h3
    · exact ⟨.qs, (onFacet_toToricExponent_iff .qs d).2 h0⟩
    · exact ⟨.pr, (onFacet_toToricExponent_iff .pr d).2 h1⟩
    · exact ⟨.sp, (onFacet_toToricExponent_iff .sp d).2 h2⟩
    · exact ⟨.rq, (onFacet_toToricExponent_iff .rq d).2 h3⟩

/-- An interior exponent of the nonnegative cone has every coordinate
strictly positive. -/
theorem coordinate_pos_of_not_mvExponentOnBoundary
    {d : Fin 4 →₀ ℕ} (h : ¬ MvExponentOnBoundary d) :
    ∀ i : Fin 4, 0 < d i := by
  rw [mvExponentOnBoundary_iff_coordinate_zero] at h
  intro i
  fin_cases i
  · exact Nat.pos_of_ne_zero (by
      intro h0
      exact h (Or.inl h0))
  · exact Nat.pos_of_ne_zero (by
      intro h1
      exact h (Or.inr (Or.inl h1)))
  · exact Nat.pos_of_ne_zero (by
      intro h2
      exact h (Or.inr (Or.inr (Or.inl h2))))
  · exact Nat.pos_of_ne_zero (by
      intro h3
      exact h (Or.inr (Or.inr (Or.inr h3))))

/-- Support of an exact initial form is inherited from the original polynomial. -/
theorem support_initialForm_subset {K : Type*} [CommSemiring K]
    (w : Fin 4 → ℤ) (m : ℤ) (p : MvPolynomial (Fin 4) K) :
    (initialForm w m p).support ⊆ p.support := by
  intro d hd
  have hne : coeff d (initialForm w m p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_initialForm] at hne
  split_ifs at hne with hw
  · exact MvPolynomial.mem_support_iff.mpr hne
  · exact (hne rfl).elim

/-- Torus-balanced support is preserved by taking an exact initial form. -/
theorem HasBalancedMvSupport.initialForm {K : Type*} [CommSemiring K]
    {a b : ℕ} {p : MvPolynomial (Fin 4) K}
    (hp : HasBalancedMvSupport a b p) (w : Fin 4 → ℤ) (m : ℤ) :
    HasBalancedMvSupport a b (initialForm w m p) := by
  intro d hd
  exact hp d (support_initialForm_subset w m p hd)

/-- Facet confinement is preserved by exact initial forms. -/
theorem MvSupportOnFacet.initialForm {K : Type*} [CommSemiring K]
    {F : HC4.Toric.ToricFacet} {p : MvPolynomial (Fin 4) K}
    (hp : MvSupportOnFacet F p) (w : Fin 4 → ℤ) (m : ℤ) :
    MvSupportOnFacet F (initialForm w m p) := by
  intro d hd
  exact hp d (support_initialForm_subset w m p hd)

end

end HC4.Polynomial
