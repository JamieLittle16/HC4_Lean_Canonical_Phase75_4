import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib.Tactic

/-!
# A singular 3x3 determinant has rank-one adjugate minors

Over a commutative ring, if det H = 0 for a 3x3 matrix, every 2x2
minor of adj(H) vanishes. This follows from the adjugate-of-adjugate
identity and does not require dividing by a principal minor.

These identities are the algebraic input for factoring the adjugate
at the cubic pole: at a rank-two point it is a rank-one matrix.
No matrix rank or field inversion is assumed in this module.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-- All 2x2 minors of the adjugate vanish when a 3x3 matrix has
zero determinant, with no symmetry hypothesis and no inverses. -/
theorem adjugate_rankOne_cross_products
    {R : Type*} [CommRing R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (hdet : H.det = 0)
    (k i j : Fin 3) :
    H.adjugate k k * H.adjugate i j =
      H.adjugate i k * H.adjugate k j := by
  classical
  let B : Matrix (Fin 3) (Fin 3) R := H.adjugate
  have hadj : B.adjugate = 0 := by
    change H.adjugate.adjugate = 0
    rw [Matrix.adjugate_adjugate H
      (by decide : Fintype.card (Fin 3) ≠ 1)]
    simp [hdet]
  have hzero (u v : Fin 3) : B.adjugate u v = 0 := by
    rw [hadj]
    rfl
  have h00 : B 1 1 * B 2 2 - B 1 2 * B 2 1 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 0 0
  have h01 : B 0 2 * B 2 1 - B 0 1 * B 2 2 = 0 := by
    have hz := hzero 0 1
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h02 : B 0 1 * B 1 2 - B 0 2 * B 1 1 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 0 2
  have h10 : B 1 2 * B 2 0 - B 1 0 * B 2 2 = 0 := by
    have hz := hzero 1 0
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h11 : B 0 0 * B 2 2 - B 0 2 * B 2 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 1 1
  have h12 : B 0 2 * B 1 0 - B 0 0 * B 1 2 = 0 := by
    have hz := hzero 1 2
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h20 : B 1 0 * B 2 1 - B 1 1 * B 2 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 2 0
  have h21 : B 0 1 * B 2 0 - B 0 0 * B 2 1 = 0 := by
    have hz := hzero 2 1
    simp [Matrix.adjugate_fin_three] at hz
    linear_combination hz
  have h22 : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hzero 2 2
  change B k k * B i j = B i k * B k j
  fin_cases k <;> fin_cases i <;> fin_cases j
  all_goals solve
    | ring
    | (change B 0 0 * B 1 1 = B 1 0 * B 0 1; linear_combination h22)
    | (change B 0 0 * B 1 2 = B 1 0 * B 0 2; linear_combination -h12)
    | (change B 0 0 * B 2 1 = B 2 0 * B 0 1; linear_combination -h21)
    | (change B 0 0 * B 2 2 = B 2 0 * B 0 2; linear_combination h11)
    | (change B 1 1 * B 0 0 = B 0 1 * B 1 0; linear_combination h22)
    | (change B 1 1 * B 0 2 = B 0 1 * B 1 2; linear_combination -h02)
    | (change B 1 1 * B 2 0 = B 2 1 * B 1 0; linear_combination -h20)
    | (change B 1 1 * B 2 2 = B 2 1 * B 1 2; linear_combination h00)
    | (change B 2 2 * B 0 0 = B 0 2 * B 2 0; linear_combination h11)
    | (change B 2 2 * B 0 1 = B 0 2 * B 2 1; linear_combination -h01)
    | (change B 2 2 * B 1 0 = B 1 2 * B 2 0; linear_combination -h10)
    | (change B 2 2 * B 1 1 = B 1 2 * B 2 1; linear_combination h00)

end
end HC4.Polynomial.RankThreeCubic
