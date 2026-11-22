import HC4.Polynomial.RankThreeCubicDetOneFirstVariationCofactor
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# The same singular determinant first variation by columns

The permutation determinant expansion picks columns directly:
its first-degree parameter coefficient contains one replacement
column. Cramer's rule identifies those determinants with the
adjugate-trace pairing without assuming det A is invertible.

The row version is already Lean-verified; this is the complementary
algebraic bridge to the polynomial determinant coefficient.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators
noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Column replacement determinant equals the corresponding row
of the adjugate acting on that replacement column. Valid even if
the original matrix is singular. -/
theorem det_updateCol_eq_adjugate_dot
    (A : Matrix ι ι R) (j : ι) (v : ι → R) :
    (A.updateCol j v).det = ∑ i : ι, A.adjugate j i * v i := by
  change (A.cramer v) j = _
  rw [Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct]

/-- Summing one-column replacement determinants is precisely the
first adjugate-trace pairing; determinant-one is not assumed. -/
theorem sum_det_updateCol_eq_adjugate_trace
    (A B : Matrix ι ι R) :
    (∑ j : ι, (A.updateCol j (fun i => B i j)).det) =
      (A.adjugate * B).trace := by
  calc
    _ = ∑ j : ι, ∑ i : ι, A.adjugate j i * B i j := by
          apply Finset.sum_congr rfl
          intro j _
          exact det_updateCol_eq_adjugate_dot A j (fun i => B i j)
    _ = (A.adjugate * B).trace := by
          simp only [Matrix.trace, Matrix.diag_apply,
            Matrix.mul_apply, dotProduct]

end
end HC4.Polynomial
