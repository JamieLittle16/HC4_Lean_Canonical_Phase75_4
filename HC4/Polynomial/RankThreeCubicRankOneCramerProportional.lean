import HC4.Polynomial.RankThreeCubicPolePrincipalCofactor
import Mathlib

/-!
# The Cramer numerator inherits rank-one adjugate geometry

If a symmetric matrix B over a domain satisfies
  B(k,k) B(i,j) = B(i,k) B(k,j),
with B(k,k) nonzero, then its column-space vector S = B r satisfies
  B(k,k) S(i) S(j) = B(i,j) S(k)^2.

This elementary algebraic lemma relates the quadratic source residue in the
actual Cramer numerator to the adjugate contraction appearing in
Jacobi's determinant derivative. The rank-one hypothesis is
explicit here; it will be derived from det(H)=0 separately.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

theorem rankOneMatrix_mulVec_proportional_products
    {R : Type*} [CommRing R] [IsDomain R]
    (B : Matrix (Fin 3) (Fin 3) R)
    (hSym : B.IsSymm)
    (r : Fin 3 → R)
    (k : Fin 3)
    (hkk : B k k ≠ 0)
    (hcross : ∀ i j : Fin 3,
      B k k * B i j = B i k * B k j)
    (i j : Fin 3) :
    B k k * (B *ᵥ r) i * (B *ᵥ r) j =
      B i j * (B *ᵥ r) k * (B *ᵥ r) k := by
  classical
  let S : Fin 3 → R := B *ᵥ r
  have hlinear (u : Fin 3) :
      B k k * S u = B u k * S k := by
    calc
      B k k * S u =
          ∑ v : Fin 3, (B k k * B u v) * r v := by
        simp [S, Matrix.mulVec, dotProduct,
          Finset.mul_sum, mul_assoc]
      _ = ∑ v : Fin 3, (B u k * B k v) * r v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hcross u v]
      _ = B u k * S k := by
        simp [S, Matrix.mulVec, dotProduct,
          Finset.mul_sum, mul_assoc]
  have hi : B k k * S i = B i k * S k := hlinear i
  have hj : B k k * S j = B j k * S k := hlinear j
  have hsym : B j k = B k j := hSym.apply j k
  have hsq : B k k * (B k k * S i * S j) =
      B k k * (B i j * S k * S k) := by
    calc
      B k k * (B k k * S i * S j) =
          (B k k * S i) * (B k k * S j) := by ring
      _ = (B i k * S k) * (B j k * S k) := by rw [hi, hj]
      _ = (B k k * B i j) * (S k * S k) := by
        rw [hsym, hcross i j]
        ring
      _ = B k k * (B i j * S k * S k) := by ring
  have hprod : B k k * S i * S j =
      B i j * S k * S k := by
    exact mul_left_cancel₀ hkk hsq
  exact hprod

end
end HC4.Polynomial.RankThreeCubic
