import HC4.Polynomial.RankThreeAffineMomentDegree
import HC4.Polynomial.HighestBinomialParallelFirstVariation
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import Mathlib.Tactic.ComputeDegree

/-!
# Degree-one endpoint moment Hessians

Both finite-staircase endpoint moment matrices come from literal affine
coefficient profiles.  Their entries therefore have longitudinal degree at
most one.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Locked endpoint moment entries have degree at most one. -/
theorem lockedBinomialMomentHessian_natDegree_le_one
    (V ell : ℕ) (a b : K) (i j : Fin 4) :
    (lockedBinomialMomentHessian V ell a b i j).natDegree ≤ 1 := by
  unfold lockedBinomialMomentHessian
  refine le_trans
    (rankThreeAffinePolynomialMomentHessian_natDegree_le
      1 (ell + 1) (V * (ell + 1)) 1
      (-1 : K) (-1 : K) (-(V : K))
      (Polynomial.C a + Polynomial.C b * Polynomial.X) i j) ?_
  compute_degree

/-- Primitive-highest endpoint moment entries have degree at most one. -/
theorem highestBinomialMomentHessian_natDegree_le_one
    (V n : ℕ) (c d : K) (i j : Fin 4) :
    (highestBinomialMomentHessian V n c d i j).natDegree ≤ 1 := by
  unfold highestBinomialMomentHessian
  refine le_trans
    (rankThreeAffinePolynomialMomentHessian_natDegree_le
      n 1 (V * n) 1
      (-1 : K) (-1 : K) (-(V : K))
      (Polynomial.C c + Polynomial.C d * Polynomial.X) i j) ?_
  compute_degree

end

end HC4.Polynomial
