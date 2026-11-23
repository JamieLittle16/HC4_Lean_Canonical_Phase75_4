import HC4.Polynomial.RankThreeCubicDetOneBorderedPrincipalCofactorSquare
import Mathlib.Tactic

/-!
# Three-scale rigidity of a principal 3x3 cofactor

For any 3x3 matrices T and A over a characteristic-zero
commutative ring, the diagonal cofactor is quadratic under
T+s*A. Its even second difference is exactly twice the
cofactor of A:

  adj(T+A)[k,k] + adj(T-A)[k,k]
   = 2*adj(T)[k,k] + 2*adj(A)[k,k].

Consequently, if determinant-one bordered matrix identities
fix the square of the SAME nonzero longitudinal response g
at the three transverse scales 0,+1,-1, then necessarily

  adj(A)[k,k] = 0.

This is the genuine obstruction mechanism to be applied to the
source's cubic leading Hessian on a pole plane. It is algebraic,
not a claim that the source specialisations are already proved.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix
noncomputable section

variable {K : Type*} [CommRing K] [CharZero K]

/-- Quadratic polarization of a diagonal 3x3 adjugate entry.
No symmetry hypothesis or matrix inverse is needed. -/
theorem principalCofactor_threeScale_polarization
    (T A : Matrix (Fin 3) (Fin 3) K) (k : Fin 3) :
    (T + A).adjugate k k + (T - A).adjugate k k =
      (2 : K) * T.adjugate k k + 2 * A.adjugate k k := by
  fin_cases k <;>
    simp [Matrix.adjugate_fin_three,
      Matrix.add_apply, Matrix.sub_apply] <;>
    ring

/-- Three determinant-one kernel-square identities with one
fixed nonzero coupling scalar force the leading cofactor to
vanish, because the diagonal cofactor is quadratic in the
transverse scaling parameter. -/
theorem principalCofactor_threeScale_square_forces_zero
    (T A : Matrix (Fin 3) (Fin 3) K) (k : Fin 3)
    (g w : K) (hg : g ≠ 0)
    (h0 : T.adjugate k k * g ^ 2 = -(w ^ 2))
    (hplus : (T + A).adjugate k k * g ^ 2 = -(w ^ 2))
    (hminus : (T - A).adjugate k k * g ^ 2 = -(w ^ 2)) :
    A.adjugate k k = 0 := by
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hpe : (T + A).adjugate k k = T.adjugate k k :=
    mul_right_cancel₀ hg2 (hplus.trans h0.symm)
  have hme : (T - A).adjugate k k = T.adjugate k k :=
    mul_right_cancel₀ hg2 (hminus.trans h0.symm)
  have hp := principalCofactor_threeScale_polarization T A k
  rw [hpe, hme] at hp
  have htwice : (2 : K) * A.adjugate k k = 0 := by
    calc
      (2 : K) * A.adjugate k k =
        T.adjugate k k + T.adjugate k k -
          2 * T.adjugate k k := by
            linear_combination -hp
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)

end
end HC4.Polynomial.RankThreeCubic
