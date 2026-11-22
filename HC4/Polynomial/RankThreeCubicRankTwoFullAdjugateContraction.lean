import HC4.Polynomial.RankThreeCubicSourceRankTwoHigherTransport
import HC4.Polynomial.RankThreeCubicAdjugateRankOneMinors
import Mathlib.Tactic

/-!
# Rank-two cubic pole: quadratic transport forces Jacobi-type cofactor contractions

On a singular symmetric 3x3 matrix over a domain, its adjugate has rank
at most one. If a nonzero kernel vector is aligned with the kth adjugate
column and the kth principal cofactor survives, any quadratic form
vanishing on that vector has zero contraction with the *entire adjugate*.

This is not limited to the time-zero derivative of the determinant.
It can be applied coefficientwise to the transported third derivatives
of the actual cubic source.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- Algebraic rank-two Jacobi contraction without fractions or an
independently chosen Cramer numerator. All hypotheses are matrix
equations over the same integral domain. -/
theorem alignedKernel_quadraticZero_implies_adjugateContraction
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (hSym : H.IsSymm)
    (hdet : H.det = 0)
    (S : Fin 3 → R)
    (k : Fin 3)
    (hkk : H.adjugate k k ≠ 0)
    (hSk : S k ≠ 0)
    (halign : ∀ i : Fin 3,
      H.adjugate k k * S i = H.adjugate i k * S k)
    (Q : Fin 3 → Fin 3 → R)
    (hquad : (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * S i * S j) = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * H.adjugate i j) = 0 := by
  classical
  let B : Matrix (Fin 3) (Fin 3) R := H.adjugate
  have hBsymm : B.IsSymm := by
    change H.adjugate.transpose = H.adjugate
    rw [Matrix.adjugate_transpose, hSym]
  have hcol :
      (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * B i k * B j k) = 0 :=
    alignedKernel_quadraticZero_implies_adjugateColumn_quadraticZero
      B S k hSk halign Q hquad
  have hcross (i j : Fin 3) :
      B k k * B i j = B i k * B j k := by
    have h := adjugate_rankOne_cross_products H hdet k i j
    change B k k * B i j = B i k * B k j at h
    rw [← hBsymm.apply k j] at h
    exact h
  have hweighted :
      B k k * (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * B i j) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * B i k * B j k) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          B k k * (Q i j * B i j) := by
            simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * B i k * B j k := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            calc
              B k k * (Q i j * B i j) =
                  Q i j * (B k k * B i j) := by ring
              _ = Q i j * (B i k * B j k) := by rw [hcross i j]
              _ = Q i j * B i k * B j k := by ring
  have hzero : B k k * (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * B i j) = 0 := hweighted.trans hcol
  exact (mul_eq_zero.mp hzero).resolve_left hkk

end
end HC4.Polynomial.RankThreeCubic
