import HC4.Polynomial.RankThreeCubicIntegrableRankOnePlaneObstruction
import Mathlib.Tactic

/-!
# A zero 3x3 adjugate forces all rank-one cross-products

For a 3x3 matrix A over any commutative ring, adj(A)=0
implies A_{kk} A_{ij}=A_{ik} A_{kj} for all indices.

This avoids introducing a matrix-rank or division hypothesis in
the rank-one Hessian-plane obstruction. The proof is a complete
finite cofactor expansion, valid over quotient domains too.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

theorem crossProducts_of_adjugate_eq_zero
    {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R)
    (hadj : A.adjugate = 0)
    (k i j : Fin 3) :
    A k k * A i j = A i k * A k j := by
  classical
  have hzero (u v : Fin 3) : A.adjugate u v = 0 := by
    rw [hadj]
    rfl
  have h00 : A 1 1 * A 2 2 - A 1 2 * A 2 1 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 0 0
  have h01 : A 0 2 * A 2 1 - A 0 1 * A 2 2 = 0 := by
    have hz := hzero 0 1
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h02 : A 0 1 * A 1 2 - A 0 2 * A 1 1 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 0 2
  have h10 : A 1 2 * A 2 0 - A 1 0 * A 2 2 = 0 := by
    have hz := hzero 1 0
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h11 : A 0 0 * A 2 2 - A 0 2 * A 2 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 1 1
  have h12 : A 0 2 * A 1 0 - A 0 0 * A 1 2 = 0 := by
    have hz := hzero 1 2
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h20 : A 1 0 * A 2 1 - A 1 1 * A 2 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 2 0
  have h21 : A 0 1 * A 2 0 - A 0 0 * A 2 1 = 0 := by
    have hz := hzero 2 1
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h22 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 2 2
  fin_cases k <;> fin_cases i <;> fin_cases j
  all_goals solve
    | ring
    | (change A 0 0 * A 1 1 = A 1 0 * A 0 1; linear_combination h22)
    | (change A 0 0 * A 1 2 = A 1 0 * A 0 2; linear_combination -h12)
    | (change A 0 0 * A 2 1 = A 2 0 * A 0 1; linear_combination -h21)
    | (change A 0 0 * A 2 2 = A 2 0 * A 0 2; linear_combination h11)
    | (change A 1 1 * A 0 0 = A 0 1 * A 1 0; linear_combination h22)
    | (change A 1 1 * A 0 2 = A 0 1 * A 1 2; linear_combination -h02)
    | (change A 1 1 * A 2 0 = A 2 1 * A 1 0; linear_combination -h20)
    | (change A 1 1 * A 2 2 = A 2 1 * A 1 2; linear_combination h00)
    | (change A 2 2 * A 0 0 = A 0 2 * A 2 0; linear_combination h11)
    | (change A 2 2 * A 0 1 = A 0 2 * A 2 1; linear_combination -h01)
    | (change A 2 2 * A 1 0 = A 1 2 * A 2 0; linear_combination -h10)
    | (change A 2 2 * A 1 1 = A 1 2 * A 2 1; linear_combination h00)

end
end HC4.Polynomial.RankThreeCubic
