import HC4.Polynomial.RankThreeCubicDetOneLowerMixedWeightZero
import Mathlib.Tactic

/-!
# Mixed-row pairing transfer along an aligned rank-two pole residue

The genuine nontriple cubic pole has a normalized source residue S
and a constant tangent direction W. Existing source transport
provides the cross-multiplication identities
  S_i * W_k = W_i * S_k.

For ANY mixed row b, its pairing with S and its pairing with W
obey exactly the same cross-multiplication identity. If both
pivot entries are nonzero over the prime quotient domain, one
pairing vanishes if and only if the other does.

This is a useful algebraic bridge for the remaining weight-zero
longitudinal mixed repair. It does NOT claim that alignment or
nonzero pivots have been assembled with the determinant-one
dichotomy in this file.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped BigOperators
noncomputable section

/-- An aligned pair of vectors has proportionally aligned
pairings with every covector, over any commutative ring. -/
theorem alignedResidue_mixedPairing_cross
    {R : Type*} [CommRing R]
    (S W b : Fin 3 → R) (k : Fin 3)
    (halign : ∀ i : Fin 3, S i * W k = W i * S k) :
    (∑ i : Fin 3, b i * S i) * W k =
      (∑ i : Fin 3, b i * W i) * S k := by
  classical
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (b i * S i) * W k =
        b i * (S i * W k) := by ring
    _ = b i * (W i * S k) := by rw [halign i]
    _ = (b i * W i) * S k := by ring

/-- In an integral domain, nonzero pivot entries make
vanishing of the mixed pairing independent of which aligned
kernel generator is used. -/
theorem alignedResidue_mixedPairing_eq_zero_iff
    {R : Type*} [CommRing R] [IsDomain R]
    (S W b : Fin 3 → R) (k : Fin 3)
    (hSk : S k ≠ 0) (hWk : W k ≠ 0)
    (halign : ∀ i : Fin 3, S i * W k = W i * S k) :
    (∑ i : Fin 3, b i * S i) = 0 ↔
      (∑ i : Fin 3, b i * W i) = 0 := by
  have hcross := alignedResidue_mixedPairing_cross S W b k halign
  constructor
  · intro hz
    rw [hz, zero_mul] at hcross
    exact (mul_eq_zero.mp hcross.symm).resolve_right hSk
  · intro hz
    rw [hz, zero_mul] at hcross
    exact (mul_eq_zero.mp hcross).resolve_right hWk

end
end HC4.Polynomial.RankThreeCubic
