import HC4.Polynomial.RankThreeCubicAdjugateRankOneMinors
import Mathlib.Tactic

/-!
# Tangent kernel residue forces annihilation of the pole normal by the adjugate

Over an integral domain a singular 3x3 matrix has rank-at-most-one
adjugate. In a principal rank-two chart its normalized kernel residue
is proportional to the chosen adjugate column. If that kernel residue
is orthogonal to a covector ell, then ell annihilates *every*
adjugate column, not merely the chosen pivot column.

This transfers pole tangency from a chosen characteristic numerator
to an intrinsic Hessian cofactor identity. No symmetry, division,
or constant-kernel assumption is needed.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- A tangent kernel aligned with a nonzero principal adjugate
column forces the pole covector to annihilate every column of
the adjugate, over any integral domain. -/
theorem alignedTangentKernel_adjugateNormal_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (hdet : H.det = 0)
    (S ell : Fin 3 → R)
    (k : Fin 3)
    (hkk : H.adjugate k k ≠ 0)
    (hSk : S k ≠ 0)
    (halign : ∀ i : Fin 3,
      H.adjugate k k * S i = H.adjugate i k * S k)
    (htangent : (∑ i : Fin 3, ell i * S i) = 0) :
    ∀ j : Fin 3,
      (∑ i : Fin 3, ell i * H.adjugate i j) = 0 := by
  classical
  have hcolK :
      (∑ i : Fin 3, ell i * H.adjugate i k) = 0 := by
    have hsum :
        H.adjugate k k * (∑ i : Fin 3, ell i * S i) =
          (∑ i : Fin 3, ell i * H.adjugate i k) * S k := by
      calc
        H.adjugate k k * (∑ i : Fin 3, ell i * S i) =
            ∑ i : Fin 3, ell i * (H.adjugate k k * S i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = ∑ i : Fin 3, ell i * (H.adjugate i k * S k) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [halign i]
        _ = (∑ i : Fin 3, ell i * H.adjugate i k) * S k := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
    have hz : (∑ i : Fin 3, ell i * H.adjugate i k) * S k = 0 := by
      rw [← hsum, htangent, mul_zero]
    exact (mul_eq_zero.mp hz).resolve_right hSk
  intro j
  have hcross (i : Fin 3) :
      H.adjugate k k * H.adjugate i j =
        H.adjugate i k * H.adjugate k j :=
    adjugate_rankOne_cross_products H hdet k i j
  have hsum :
      H.adjugate k k * (∑ i : Fin 3, ell i * H.adjugate i j) =
        (∑ i : Fin 3, ell i * H.adjugate i k) * H.adjugate k j := by
    calc
      H.adjugate k k * (∑ i : Fin 3, ell i * H.adjugate i j) =
          ∑ i : Fin 3, ell i * (H.adjugate k k * H.adjugate i j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ i : Fin 3, ell i * (H.adjugate i k * H.adjugate k j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hcross i]
      _ = (∑ i : Fin 3, ell i * H.adjugate i k) * H.adjugate k j := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hz : H.adjugate k k * (∑ i : Fin 3, ell i * H.adjugate i j) = 0 := by
    rw [hsum, hcolK, zero_mul]
  exact (mul_eq_zero.mp hz).resolve_left hkk

end
end HC4.Polynomial.RankThreeCubic
