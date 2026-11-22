import HC4.Polynomial.RankThreeCubicDetOneWeightFiveSourceGap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# First determinant variation: row replacement and adjugate trace

The determinant is multilinear in its rows. Its first variation
along a matrix B is the sum of determinants obtained by replacing
exactly one row of A by the corresponding row of B.

This file identifies that coefficient with the adjugate trace
pairing over an arbitrary commutative ring, even for SINGULAR A.
In the cubic HC4 application det(Hess L3)=0, so no invertibility
hypothesis may be introduced.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators
noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Replacing a matrix row never changes the cofactors of that
same row. This is an identity for arbitrary matrices. -/
theorem adjugate_updateRow_same_col
    (A : Matrix ι ι R) (i j : ι) (v : ι → R) :
    (A.updateRow i v).adjugate j i = A.adjugate j i := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  congr 1
  apply Matrix.ext
  intro k l
  by_cases h : k = i
  · subst k
    simp [Matrix.updateRow_apply]
  · simp [Matrix.updateRow_apply, h]

/-- Laplace expansion in a replaced row uses the adjugate
of the ORIGINAL matrix, not the updated one. -/
theorem det_updateRow_eq_cofactor_pairing
    (A : Matrix ι ι R) (i : ι) (v : ι → R) :
    (A.updateRow i v).det =
      ∑ j : ι, v j * A.adjugate j i := by
  rw [Matrix.det_eq_sum_mul_adjugate_row (A.updateRow i v) i]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.updateRow_self, adjugate_updateRow_same_col]

/-- First determinant variation in row-replacement form is
exactly the adjugate-trace pairing, without dividing by det A. -/
theorem sum_det_updateRow_eq_adjugate_trace
    (A B : Matrix ι ι R) :
    (∑ i : ι, (A.updateRow i (B i)).det) =
      (A.adjugate * B).trace := by
  calc
    (∑ i : ι, (A.updateRow i (B i)).det) =
        ∑ i : ι, ∑ j : ι, B i j * A.adjugate j i := by
          apply Finset.sum_congr rfl
          intro i _
          exact det_updateRow_eq_cofactor_pairing A i (B i)
    _ = ∑ j : ι, ∑ i : ι, A.adjugate j i * B i j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
    _ = (A.adjugate * B).trace := by
          simp only [Matrix.trace, Matrix.mul_apply, dotProduct]

end
end HC4.Polynomial
