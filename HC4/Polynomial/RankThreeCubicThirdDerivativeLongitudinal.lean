import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic

/-!
# Cubic third derivatives descend to longitudinal polynomials

Three transverse derivatives of a transverse-weight-three source
have weight zero. Since longitudinal weight is zero and the three
transverse weights are all one, every monomial in such a derivative
is independent of the transverse variables.

This module gives a direct *source polynomial* representation of each
third derivative as a polynomial in the one longitudinal variable.
This is not an added endpoint hypothesis and requires no rational
characteristic or determinant squarefreeness.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial Finsupp
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- Every source monomial's cubic transverse weight is precisely the
sum of its three transverse exponents. -/
theorem transverseCubicWeight_eq_transverseSum
    (m : (Unit ⊕ Fin 3) →₀ ℕ) :
    Finsupp.weight transverseCubicWeight m =
      (m (.inr 0) : ℤ) + (m (.inr 1) : ℤ) + (m (.inr 2) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [Fintype.sum_sum_type, Fin.sum_univ_three,
      transverseCubicWeight]
  · intro i
    simp

/-- Weight-zero polynomials cannot contain any of the three transverse
source variables, including when their longitudinal degree is unbounded. -/
theorem transverseWeightZero_supported_only_longitudinal
    (P : SB K)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight 0) :
    ∀ m : (Unit ⊕ Fin 3) →₀ ℕ,
      MvPolynomial.coeff m P ≠ 0 →
      ∀ j : Fin 3, m (.inr j) = 0 := by
  intro m hm j
  have hw := hP hm
  rw [transverseCubicWeight_eq_transverseSum] at hw
  fin_cases j <;> omega

/-- Source weight zero yields an actual polynomial in the sole
longitudinal variable; no localization or denominator is involved. -/
theorem exists_longitudinal_polynomial_of_transverseWeightZero
    (P : SB K)
    (hP : P.IsWeightedHomogeneous transverseCubicWeight 0) :
    ∃ T : MvPolynomial Unit K,
      MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T = P := by
  classical
  have hsupp :=
    transverseWeightZero_supported_only_longitudinal P hP
  have hnotin (j : Fin 3) : Sum.inr j ∉ P.vars := by
    intro hmem
    obtain ⟨m, hm, hvar⟩ :=
      (MvPolynomial.mem_vars_iff_mem_support (Sum.inr j)).mp hmem
    have hc : MvPolynomial.coeff m P ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    have he : m (.inr j) = 0 := hsupp m hc j
    have hne : m (.inr j) ≠ 0 := by
      simpa only [Finsupp.mem_support_iff] using hvar
    exact hne he
  have hrange :
      (↑P.vars : Set (Unit ⊕ Fin 3)) ⊆
        Set.range (Sum.inl : Unit → Unit ⊕ Fin 3) := by
    intro i hi
    cases i with
    | inl u => exact ⟨u, rfl⟩
    | inr j => exact False.elim (hnotin j hi)
  exact MvPolynomial.exists_rename_eq_of_vars_subset_range
    P (Sum.inl : Unit → Unit ⊕ Fin 3)
    (by intro x y h; exact Sum.inl_injective h) hrange

/-- Actual cubic-source triple transverse derivatives are longitudinal
polynomials, regardless of the chosen longitudinal slice. -/
theorem exists_sourceCubic_thirdTransverse_longitudinal
    (F : SB K) (i j k : Fin 3) :
    let L := initialForm transverseCubicWeight 3 F
    let Q := pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
    ∃ T : MvPolynomial Unit K,
      MvPolynomial.rename (Sum.inl : Unit → Unit ⊕ Fin 3) T = Q := by
  let L := initialForm transverseCubicWeight 3 F
  let Q := pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))
  have hL : L.IsWeightedHomogeneous transverseCubicWeight 3 :=
    initialForm_isWeightedHomogeneous transverseCubicWeight 3 F
  have h1 := pderiv_isWeightedHomogeneous hL (.inr i)
  have h2 := pderiv_isWeightedHomogeneous h1 (.inr j)
  have h3 := pderiv_isWeightedHomogeneous h2 (.inr k)
  have hQ : Q.IsWeightedHomogeneous transverseCubicWeight 0 := by
    simpa [Q, transverseCubicWeight] using h3
  exact exists_longitudinal_polynomial_of_transverseWeightZero Q hQ

end
end HC4.Polynomial.RankThreeCubic
