import HC4.Valuation.AdaptiveAlignedSmithFirstContactQuadraticWeightRestriction
import HC4.Newton.TerminalWeightPermutation
import Mathlib.Tactic

/-!
# Square first-contact elimination on the terminal two-zero boundary

The previous green module shows that an honest square first-contact monomial
`X_i^2` forces the corresponding terminal source weight to be positive, while
the marked terminal collision forces a second zero-weight coordinate away
from both the marked longitudinal coordinate `0` and from `i`.

This file closes the resulting finite weight configuration.

A nondegenerate terminal Hessian supplies a complement-weight permutation

    w_(pi r) + w_r = d.

Summing over the four coordinates gives

    sum_r w_r = 2 d.

Hence if two distinct coordinates have weight zero, the remaining two weights
must both equal `d` (every terminal weight is already known to be at most
`d`).  But a square contact requires

    2 w_i = d.

Since its coordinate is not one of the two zero coordinates, it must have
weight `d`, forcing `2 d = d`, contradicting the positive terminal degree.

Thus an honest surviving first-contact terminal collision can never have a
square distinguished contact.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- The complement matching of the nondegenerate terminal Hessian forces the
sum of the four terminal source weights to be twice the terminal weighted
degree. -/
theorem totalWeight_eq_two_degree
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    (∑ i : Fin 4, (C.weight i : ℤ)) = 2 * (C.degree : ℤ) := by
  rcases
      nonScalarTerminalConformalFace_has_complementWeightPermutation
        C.residualNonScalarJump.1 with
    ⟨pi, hpi⟩
  have hsum :
      (∑ i : Fin 4,
          ((C.weight (pi i) : ℤ) + (C.weight i : ℤ))) =
        ∑ _i : Fin 4, (C.degree : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpi i
  have hperm :
      (∑ i : Fin 4, (C.weight (pi i) : ℤ)) =
        ∑ i : Fin 4, (C.weight i : ℤ) := by
    simpa using
      (Equiv.sum_comp pi (fun i : Fin 4 => (C.weight i : ℤ)))
  rw [Finset.sum_add_distrib, hperm] at hsum
  have hbalance :
      2 * (∑ i : Fin 4, (C.weight i : ℤ)) =
        4 * (C.degree : ℤ) := by
    simpa [two_mul, Fin.sum_univ_four] using hsum
  linarith

/-- If `0` and a second distinct coordinate `z` have terminal weight zero,
then every coordinate outside `{0,z}` has the full terminal degree weight.
This is the four-dimensional finite consequence of `sum w_i = 2d` and
`w_i <= d`. -/
theorem weight_eq_degree_of_secondZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (z i : Fin 4)
    (hz0 : z ≠ 0)
    (hzw : C.weight z = 0)
    (hi0 : i ≠ 0)
    (hiz : i ≠ z) :
    C.weight i = C.degree := by
  have htotal := C.totalWeight_eq_two_degree
  have htotal4 :
      (C.weight 0 : ℤ) + (C.weight 1 : ℤ) +
          (C.weight 2 : ℤ) + (C.weight 3 : ℤ) =
        2 * (C.degree : ℤ) := by
    simpa [Fin.sum_univ_four] using htotal
  have h0 : C.weight (0 : Fin 4) = 0 := C.weight_zero
  have hle0 := C.weight_le_degree (0 : Fin 4)
  have hle1 := C.weight_le_degree (1 : Fin 4)
  have hle2 := C.weight_le_degree (2 : Fin 4)
  have hle3 := C.weight_le_degree (3 : Fin 4)
  fin_cases z <;> fin_cases i <;>
    simp_all <;> omega

/-- **Square-contact terminal contradiction, without JC2.**

An honest first-contact terminal cocharacter cannot survive when the
selected first-contact monomial is a square `X_i^2`.
-/
theorem impossible_of_squareContact
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4)
    (hsquare :
      T.lattice.contactExponent =
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
          i i) :
    False := by
  have hiPos : 0 < C.weight i :=
    C.squareContact_weight_pos i hsquare
  have hi0 : i ≠ 0 := by
    intro hi
    subst i
    rw [C.weight_zero] at hiPos
    omega
  rcases C.exists_secondMarkedZero_away_from_squareContact i hsquare with
    ⟨z, hz0, hzi, hzw⟩
  have hiz : i ≠ z := by
    exact Ne.symm hzi
  have hiDegree : C.weight i = C.degree :=
    C.weight_eq_degree_of_secondZero z i hz0 hzw hi0 hiz
  have hsum := C.quadraticContact_weightSum i i hsquare
  have hdpos : 0 < (C.degree : ℤ) := C.degree_pos
  rw [hiDegree] at hsum
  linarith

/-- Proposition-level form convenient for the eventual source-lift theorem. -/
theorem not_squareContact
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T)
    (i : Fin 4) :
    T.lattice.contactExponent ≠
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent
        i i := by
  intro hsquare
  exact C.impossible_of_squareContact i hsquare

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
