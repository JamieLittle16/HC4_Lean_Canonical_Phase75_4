module

public import HC4.Polynomial.RankThreeCubicRankOneCramerProportional
public import Mathlib.Tactic

/-!
# Rank-one Cramer quadratic vanishing forces adjugate contraction vanishing

Over any integral domain, a symmetric rank-one matrix B with a nonzero
diagonal pivot and a nonzero Cramer vector S=B*r has the property that

  Σᵢⱼ Qᵢⱼ Sᵢ Sⱼ = 0 ⇒ Σᵢⱼ Qᵢⱼ Bᵢⱼ = 0.

This is the cancellation bridge from the source-derived singular
residue quadratic identities to Jacobi's determinant-derivative
contraction. It does not assert the pole obstruction is impossible.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

theorem rankOneCramer_quadratic_zero_implies_adjugate_contraction_zero
    (B : Matrix (Fin 3) (Fin 3) R)
    (hSym : B.IsSymm)
    (r : Fin 3 → R)
    (k : Fin 3)
    (hkk : B k k ≠ 0)
    (hcross : ∀ i j : Fin 3,
      B k k * B i j = B i k * B k j)
    (hS : B *ᵥ r ≠ 0)
    (Q : Fin 3 → Fin 3 → R)
    (hquad :
      (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * (B *ᵥ r) i * (B *ᵥ r) j) = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j * B i j) = 0 := by
  classical
  let S : Fin 3 → R := B *ᵥ r
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 3, S i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hS
    funext i
    exact h i
  have hk : S k ≠ 0 := by
    intro hzero
    have hprod :=
      rankOneMatrix_mulVec_proportional_products
        B hSym r k hkk hcross i₀ i₀
    have hne : B k k * S i₀ * S i₀ ≠ 0 :=
      mul_ne_zero (mul_ne_zero hkk hi₀) hi₀
    apply hne
    simpa only [S, hzero, mul_zero] using hprod
  have hweighted :
      B k k * (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * S i * S j) =
      (S k * S k) * (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j * B i j) := by
    calc
      B k k * (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * S i * S j) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          B k k * (Q i j * S i * S j) := by
            simp only [Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (S k * S k) * (Q i j * B i j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            have hij :=
              rankOneMatrix_mulVec_proportional_products
                B hSym r k hkk hcross i j
            change B k k * S i * S j =
              B i j * S k * S k at hij
            rw [show B k k * (Q i j * S i * S j) =
                  Q i j * (B k k * S i * S j) by ring,
                hij]
            ring
      _ = (S k * S k) * (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j * B i j) := by
            simp only [Finset.mul_sum]
  have hzero : (S k * S k) *
      (∑ i : Fin 3, ∑ j : Fin 3, Q i j * B i j) = 0 := by
    rw [hquad] at hweighted
    simpa only [mul_zero] using hweighted.symm
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hk hk)

end
end HC4.Polynomial.RankThreeCubic
