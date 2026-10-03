import HC4.Polynomial.MatrixPolynomialReflect
import Mathlib.Tactic

/-!
# Cubic coefficient of a four-by-four linear matrix pencil by reflection

For a `4 x 4` matrix pencil

    A + t B,

entrywise reflection at degree one swaps the endpoints and determinant
reflection occurs at degree four.  Consequently the cubic determinant
coefficient from the `A` end is exactly the linear determinant coefficient
from the `B` end:

    [t^3] det(A + t B) = [t] det(B + t A).

This is the state-free bridge which turns the remaining A19 cubic self
variation into an ordinary dual-number first variation around the interior
pure mode.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- A literal linear polynomial matrix pencil. -/
noncomputable def linearMatrixPencil
    (A B : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) (Polynomial R) :=
  fun i j => Polynomial.C (A i j) + Polynomial.monomial 1 (B i j)

/-- Every entry of a linear matrix pencil has degree at most one. -/
theorem linearMatrixPencil_natDegree_le_one
    (A B : Matrix (Fin 4) (Fin 4) R) (i j : Fin 4) :
    (linearMatrixPencil A B i j).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  simp [linearMatrixPencil, Polynomial.coeff_monomial, hn0, hn1]

/-- Reflecting a linear pencil at degree one swaps its two matrix
coefficients. -/
theorem reflectMatrix_one_linearMatrixPencil
    (A B : Matrix (Fin 4) (Fin 4) R) :
    reflectMatrix 1 (linearMatrixPencil A B) =
      linearMatrixPencil B A := by
  apply Matrix.ext
  intro i j
  apply Polynomial.ext
  intro n
  simp [reflectMatrix, linearMatrixPencil, Polynomial.coeff_reflect,
    Polynomial.coeff_monomial]
  by_cases hn0 : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  · have hrev : Polynomial.revAt 1 n = n := by
      apply Polynomial.revAt_eq_self_of_lt
      omega
    rw [hrev]
    simp [hn0, hn1]

/-- **Cubic/linear reflection identity for `4 x 4` pencils.** -/
theorem coeff_three_det_linearMatrixPencil_eq_coeff_one_reverse
    (A B : Matrix (Fin 4) (Fin 4) R) :
    (linearMatrixPencil A B).det.coeff 3 =
      (linearMatrixPencil B A).det.coeff 1 := by
  have hdeg : ∀ i j,
      (linearMatrixPencil A B i j).natDegree ≤ 1 := by
    intro i j
    exact linearMatrixPencil_natDegree_le_one A B i j
  have hreflect := det_reflectMatrix (linearMatrixPencil A B) 1 hdeg
  rw [reflectMatrix_one_linearMatrixPencil] at hreflect
  have hc := congrArg (fun p : Polynomial R => p.coeff 1) hreflect
  simp only [Polynomial.coeff_reflect] at hc
  have hcard : Fintype.card (Fin 4) * 1 = 4 := by decide
  rw [hcard] at hc
  have hrev : Polynomial.revAt 4 1 = 3 := by
    rw [Polynomial.revAt_le (by omega)]
  rw [hrev] at hc
  exact hc.symm

end

end HC4.Polynomial
