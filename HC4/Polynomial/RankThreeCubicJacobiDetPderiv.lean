module

public import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
public import Mathlib.Tactic

/-!
# Three-dimensional Jacobi formula for a polynomial matrix

We prove the derivative-of-determinant identity directly for a 3x3
matrix with multivariate polynomial entries, without assuming that
the matrix is invertible. The resulting formula is valid at singular
points and hence at every irreducible factor of its determinant.

This formula identifies the gradient of a transverse Hessian
determinant with the contraction of its adjugate and the
third-derivative matrices. It will be combined with the source
cubic pole quadratic-residue equations in a separate theorem.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- Jacobi's determinant derivative identity for a polynomial 3x3
matrix, including singular matrices: no inverse is used. -/
theorem pderiv_det_fin_three
    {K : Type*} [Field K]
    (H : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K))
    (i : Fin 3) :
    pderiv i H.det =
      ∑ j : Fin 3, ∑ k : Fin 3,
        H.adjugate k j * pderiv i (H j k) := by
  classical
  rw [Matrix.det_fin_three]
  simp only [Fin.sum_univ_three, MvPolynomial.pderiv_mul,
    map_add, map_sub]
  simp [Matrix.adjugate_fin_three, Fin.sum_univ_three]
  ring

end
end HC4.Polynomial.RankThreeCubic
