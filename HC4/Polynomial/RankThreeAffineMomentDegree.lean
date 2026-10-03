import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Tactic.ComputeDegree

/-!
# Degree bound for affine rank-three moment Hessians

Every entry of a rank-three affine moment Hessian is a linear combination of
the profile and its first two Euler derivatives.  Euler differentiation does
not increase polynomial degree, so no moment entry has longitudinal degree
larger than the profile itself.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Entrywise longitudinal degree bound by the coefficient-profile degree. -/
theorem rankThreeAffinePolynomialMomentHessian_natDegree_le
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i j : Fin 4) :
    (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi i j).natDegree ≤
      phi.natDegree := by
  rw [rankThreeAffinePolynomialMomentHessian_apply]
  compute_degree

/-- Parallel-staircase specialization of the generic degree bound. -/
theorem parallelStaircaseMomentHessian_natDegree_le
    (V k j : ℕ) (phi : Polynomial K) (i l : Fin 4) :
    (parallelStaircaseMomentHessian V k j phi i l).natDegree ≤ phi.natDegree := by
  exact rankThreeAffinePolynomialMomentHessian_natDegree_le
    k (j + 1) (V * (k + j)) 1 (-1 : K) (-1 : K) (-(V : K)) phi i l

end

end HC4.Polynomial
