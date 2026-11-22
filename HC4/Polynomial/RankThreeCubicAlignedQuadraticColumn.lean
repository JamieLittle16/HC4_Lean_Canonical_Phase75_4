import HC4.Polynomial.RankThreeCubicSourceRankTwoAdjugateAlignment
import Mathlib.Tactic

/-!
# Transfer quadratic identities to an adjugate-column direction

In a principal rank-two chart over a domain, the nonzero normalized
kernel S is aligned with an adjugate column B(-,k):
    B(k,k) * S(i) = B(i,k) * S(k).
The scalar S(k) is nonzero, so an arbitrary quadratic contraction
vanishing on S also vanishes on that adjugate column.

This lemma is valid for *each characteristic-time coefficient*
and requires no squarefreeness, no matrix inversion, and no
assumption that B(k,k) is a unit.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A quadratic form annihilating a nonzero aligned kernel vector
also annihilates the corresponding adjugate-column direction. -/
theorem alignedKernel_quadraticZero_implies_adjugateColumn_quadraticZero
    {R : Type*} [CommRing R] [IsDomain R]
    (B : Matrix (Fin 3) (Fin 3) R)
    (S : Fin 3 → R)
    (k : Fin 3)
    (hSk : S k ≠ 0)
    (halign : ∀ i : Fin 3,
      B k k * S i = B i k * S k)
    (Q : Fin 3 → Fin 3 → R)
    (hquad :
      (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * S i * S j) = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j * B i k * B j k) = 0 := by
  classical
  have hweighted :
      B k k * B k k *
        (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * S i * S j) =
      S k * S k *
        (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * B i k * B j k) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          B k k * B k k * (Q i j * S i * S j) := by
            simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          S k * S k * (Q i j * B i k * B j k) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            calc
              B k k * B k k * (Q i j * S i * S j) =
                  Q i j * (B k k * S i) * (B k k * S j) := by ring
              _ = Q i j * (B i k * S k) * (B j k * S k) := by
                    rw [halign i, halign j]
              _ = S k * S k * (Q i j * B i k * B j k) := by ring
      _ = S k * S k *
          (∑ i : Fin 3, ∑ j : Fin 3,
            Q i j * B i k * B j k) := by
            simp only [Finset.mul_sum]
  have hzero :
      (S k * S k) *
        (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * B i k * B j k) = 0 := by
    rw [hquad] at hweighted
    simpa only [mul_zero] using hweighted.symm
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hSk hSk)

end
end HC4.Polynomial.RankThreeCubic
