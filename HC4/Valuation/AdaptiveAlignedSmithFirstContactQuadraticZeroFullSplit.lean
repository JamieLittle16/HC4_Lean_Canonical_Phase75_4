import HC4.Valuation.AdaptiveAlignedSmithFirstContactSquareContactElimination
import Mathlib.Tactic

/-!
# Zero/full splitting of a surviving quadratic first contact

The previous terminal arithmetic has now proved three facts for an honest
first-contact terminal cocharacter:

* the marked longitudinal source weight is zero;
* a second distinct zero weight is forced;
* the total source weight is exactly twice the terminal degree, so every
  coordinate away from the two zero-weight axes has full weight `d`.

At the same time a distinguished quadratic first-contact monomial `X_i X_k`
has weighted degree exactly `d`.

Consequently a surviving quadratic contact is forced to straddle the
zero/full boundary:

    (w_i,w_k) = (0,d)  or  (d,0).

In particular `i != k`; the square case is already impossible, and a
quadratic contact cannot use two positive-weight directions either.

This is the finite terminal geometry needed by the source-lift step.  If the
rank-one kernel contact lifts to a quadratic source contact whose two source
directions are both forced positive by the retained Hessian chart, terminal
closure is impossible without any JC2 input.  Conversely, any surviving
quadratic terminal contact must expose one of its two directions as the
second zero-weight direction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- Relative to the marked zero and any second terminal zero, every source
coordinate has either zero terminal weight or the full terminal degree. -/
theorem weight_eq_zero_or_degree
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4) :
    C.weight i = 0 ∨ C.weight i = C.degree := by
  rcases C.hasSecondMarkedTerminalZero with ⟨z, hz0, hzw⟩
  by_cases hi0 : i = 0
  · left
    simpa [hi0] using C.weight_zero
  · by_cases hiz : i = z
    · left
      simpa [hiz] using hzw
    · right
      exact C.weight_eq_degree_of_secondZero z i hz0 hzw hi0 hiz

/-- **Quadratic zero/full split.**

Every surviving distinguished quadratic first-contact monomial has exactly
one zero-weight coordinate and one full-degree coordinate. -/
theorem quadraticContact_zero_full_split
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k) :
    (C.weight i = 0 ∧ C.weight k = C.degree) ∨
      (C.weight k = 0 ∧ C.weight i = C.degree) := by
  rcases C.weight_eq_zero_or_degree i with hi0 | hid
  · rcases C.weight_eq_zero_or_degree k with hk0 | hkd
    · exact False.elim
        (C.not_both_zero_of_quadraticContact i k hquad ⟨hi0, hk0⟩)
    · exact Or.inl ⟨hi0, hkd⟩
  · rcases C.weight_eq_zero_or_degree k with hk0 | hkd
    · exact Or.inr ⟨hk0, hid⟩
    · have hsum := C.quadraticContact_weightSum i k hquad
      have hdpos : 0 < (C.degree : ℤ) := C.degree_pos
      rw [hid, hkd] at hsum
      exfalso
      linarith

/-- A surviving quadratic contact cannot be a square.  This is a convenient
index-level corollary of the already-green square-contact elimination. -/
theorem quadraticContact_indices_ne
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k) :
    i ≠ k := by
  intro hik
  subst k
  exact C.impossible_of_squareContact i hquad

/-- If neither coordinate of a surviving quadratic contact is the marked
longitudinal axis, then one of those two transverse coordinates itself is a
zero-weight direction. -/
theorem quadraticContact_has_transverse_zero_of_avoids_markedAxis
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k)
    (hi0 : i ≠ 0)
    (hk0 : k ≠ 0) :
    (C.weight i = 0 ∧ C.weight k = C.degree) ∨
      (C.weight k = 0 ∧ C.weight i = C.degree) := by
  exact C.quadraticContact_zero_full_split i k hquad

/-- If both directions occurring in a quadratic contact are known to have
positive terminal weight, the terminal first-contact branch is impossible. -/
theorem impossible_of_quadraticContact_both_positive
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i k : Fin 4)
    (hquad :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i k)
    (hi : 0 < C.weight i)
    (hk : 0 < C.weight k) :
    False := by
  rcases C.quadraticContact_zero_full_split i k hquad with h | h
  · rw [h.1] at hi
    omega
  · rw [h.1] at hk
    omega

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
