import HC4.Polynomial.MatrixPolynomialReflect
import Mathlib.Tactic

/-!
# Top coefficient of a bounded polynomial matrix determinant

If every entry of an `n x n` polynomial matrix has degree at most `N`, then
the coefficient of degree `card(n) * N` in its determinant is exactly the
determinant of the matrix of degree-`N` entry coefficients.

The proof is a one-line consequence of matrix reflection: reflect every entry
at `N`, use determinant reflection at `card(n) * N`, and take constant
coefficients.  This is the reusable top-longitudinal-coefficient bridge for the
final A19 finite-staircase argument.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- Constant coefficient commutes with determinant. -/
theorem coeff_zero_det_polynomialMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial R)) :
    M.det.coeff 0 =
      (Matrix.of fun i j => (M i j).coeff 0).det := by
  let ev : Polynomial R →+* R := Polynomial.evalRingHom 0
  have h := ev.map_det M
  change Polynomial.eval 0 M.det =
    (ev.mapMatrix M).det at h
  have hmatrix :
      ev.mapMatrix M = Matrix.of fun i j => (M i j).coeff 0 := by
    apply Matrix.ext
    intro i j
    simp [ev, Polynomial.coeff_zero_eq_eval_zero]
  rw [hmatrix] at h
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

/-- The constant coefficient of reflection at `N` is the original coefficient
at `N`. -/
theorem coeff_zero_reflect
    (N : ℕ) (p : Polynomial R) :
    (Polynomial.reflect N p).coeff 0 = p.coeff N := by
  rw [Polynomial.coeff_reflect]
  simp [Polynomial.revAt]

/-- **Top determinant coefficient from top entry coefficients.** -/
theorem coeff_card_mul_top_det_polynomialMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial R)) (N : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ N) :
    M.det.coeff (Fintype.card n * N) =
      (Matrix.of fun i j => (M i j).coeff N).det := by
  have hreflect := det_reflectMatrix M N hdeg
  have hzero := coeff_zero_det_polynomialMatrix (reflectMatrix N M)
  have hdetCoeff :
      (Polynomial.reflect (Fintype.card n * N) M.det).coeff 0 =
        M.det.coeff (Fintype.card n * N) :=
    coeff_zero_reflect (Fintype.card n * N) M.det
  calc
    M.det.coeff (Fintype.card n * N) =
        (Polynomial.reflect (Fintype.card n * N) M.det).coeff 0 :=
      hdetCoeff.symm
    _ = (reflectMatrix N M).det.coeff 0 := by rw [hreflect]
    _ = (Matrix.of fun i j => (reflectMatrix N M i j).coeff 0).det := hzero
    _ = (Matrix.of fun i j => (M i j).coeff N).det := by
      congr 1
      apply Matrix.ext
      intro i j
      exact coeff_zero_reflect N (M i j)

end

end HC4.Polynomial
