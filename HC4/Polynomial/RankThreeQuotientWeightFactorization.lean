import HC4.Polynomial.RankThreeQuotientFibers
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-!
# Weights factoring through rank-three quotient coordinates

A linear weight on exponent space which is constant along the primitive
direction

    (1,-1,-alpha,-beta)

must factor through the quotient invariants

    pair = e0+e1,
    first = alpha*e0+e2,
    second = beta*e0+e3.

This is the elementary linear algebra behind the remaining A19 planar-carrier
reconstruction.  It is state-free and works over integer weights.
-/

namespace HC4.Polynomial

noncomputable section

/-- An integer exponent weight annihilates the primitive rank-three direction
exactly when its coordinate-0 coefficient is the indicated combination of the
other three coefficients. -/
def RankThreeDirectionNeutralWeight
    (alpha beta : ℕ) (w : Fin 4 → ℤ) : Prop :=
  w 0 = w 1 + (alpha : ℤ) * w 2 + (beta : ℤ) * w 3

/-- The linear form induced by a neutral source weight on quotient space. -/
def rankThreeQuotientWeight
    (w : Fin 4 → ℤ) (q : RankThreeQuotientCoordinate) : ℤ :=
  w 1 * (q.pair : ℤ) +
    w 2 * (q.firstTransverse : ℤ) +
    w 3 * (q.secondTransverse : ℤ)

/-- **Neutral-weight factorization.**  A weight annihilating the primitive
line direction depends only on the quotient coordinate. -/
theorem finsupp_weight_eq_rankThreeQuotientWeight
    (alpha beta : ℕ) (w : Fin 4 → ℤ)
    (hneutral : RankThreeDirectionNeutralWeight alpha beta w)
    (e : Fin 4 →₀ ℕ) :
    Finsupp.weight w e =
      rankThreeQuotientWeight w
        (rankThreeQuotientCoordinate alpha beta e) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp only [rankThreeQuotientWeight,
      rankThreeQuotientCoordinate_pair,
      rankThreeQuotientCoordinate_firstTransverse,
      rankThreeQuotientCoordinate_secondTransverse]
    rw [hneutral]
    push_cast
    ring
  · intro i
    simp

/-- Consequently equal quotient coordinates have equal value for every neutral
weight. -/
theorem finsupp_weight_eq_of_rankThreeQuotientCoordinate_eq
    (alpha beta : ℕ) (w : Fin 4 → ℤ)
    (hneutral : RankThreeDirectionNeutralWeight alpha beta w)
    {e f : Fin 4 →₀ ℕ}
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f) :
    Finsupp.weight w e = Finsupp.weight w f := by
  rw [finsupp_weight_eq_rankThreeQuotientWeight alpha beta w hneutral e,
    finsupp_weight_eq_rankThreeQuotientWeight alpha beta w hneutral f, hq]

/-- Conversely, if two exponents differ by one exact primitive step and a
weight takes the same value on them, the weight is direction-neutral. -/
theorem rankThreeDirectionNeutralWeight_of_primitive_pair
    (alpha beta : ℕ) (w : Fin 4 → ℤ)
    (e f : Fin 4 →₀ ℕ)
    (h0 : f 0 = e 0 + 1)
    (h1 : e 1 = f 1 + 1)
    (h2 : e 2 = f 2 + alpha)
    (h3 : e 3 = f 3 + beta)
    (hw : Finsupp.weight w e = Finsupp.weight w f) :
    RankThreeDirectionNeutralWeight alpha beta w := by
  unfold RankThreeDirectionNeutralWeight
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_fintype, Finsupp.sum_fintype] at hw
  · rw [Fin.sum_univ_four] at hw
    norm_num at hw
    push_cast at hw
    omega
  · intro i
    simp
  · intro i
    simp

end

end HC4.Polynomial
