import HC4.Polynomial.TwoFunctionMixedOrientationRigidity
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Rank-three quotient fibers

For a primitive source-line direction

    (1, -1, -alpha, -beta)

it is useful to quotient exponent space before reconstructing the A19 carrier.
The three integral invariants are

    p = e0 + e1,
    r = alpha * e0 + e2,
    s = beta * e0 + e3.

This file contains only the finite-lattice bookkeeping.  It deliberately knows
nothing about A19, contact clocks, singularity, or source coefficients.
-/

namespace HC4.Polynomial

noncomputable section

/-- Integral coordinates on the quotient by the rank-three line direction
`(1,-1,-alpha,-beta)`. -/
structure RankThreeQuotientCoordinate where
  pair : ℕ
  firstTransverse : ℕ
  secondTransverse : ℕ
  deriving DecidableEq

/-- Quotient coordinate of a four-variable exponent. -/
def rankThreeQuotientCoordinate
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) : RankThreeQuotientCoordinate :=
  {
    pair := e 0 + e 1
    firstTransverse := alpha * e 0 + e 2
    secondTransverse := beta * e 0 + e 3
  }

@[simp] theorem rankThreeQuotientCoordinate_pair
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) :
    (rankThreeQuotientCoordinate alpha beta e).pair = e 0 + e 1 := rfl

@[simp] theorem rankThreeQuotientCoordinate_firstTransverse
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) :
    (rankThreeQuotientCoordinate alpha beta e).firstTransverse =
      alpha * e 0 + e 2 := rfl

@[simp] theorem rankThreeQuotientCoordinate_secondTransverse
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) :
    (rankThreeQuotientCoordinate alpha beta e).secondTransverse =
      beta * e 0 + e 3 := rfl

/-- Equality in the quotient is exactly the three invariant equations. -/
theorem rankThreeQuotientCoordinate_eq_iff
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ) :
    rankThreeQuotientCoordinate alpha beta e =
        rankThreeQuotientCoordinate alpha beta f ↔
      e 0 + e 1 = f 0 + f 1 ∧
      alpha * e 0 + e 2 = alpha * f 0 + f 2 ∧
      beta * e 0 + e 3 = beta * f 0 + f 3 := by
  constructor
  · intro h
    have hp := congrArg RankThreeQuotientCoordinate.pair h
    have hr := congrArg RankThreeQuotientCoordinate.firstTransverse h
    have hs := congrArg RankThreeQuotientCoordinate.secondTransverse h
    exact ⟨hp, hr, hs⟩
  · rintro ⟨hp, hr, hs⟩
    apply RankThreeQuotientCoordinate.ext <;> assumption

/-- Inside one quotient fiber, the longitudinal coordinate determines the
entire source exponent. -/
theorem eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f)
    (h0 : e 0 = f 0) :
    e = f := by
  rw [rankThreeQuotientCoordinate_eq_iff] at hq
  rcases hq with ⟨hp, hr, hs⟩
  ext i
  fin_cases i
  · exact h0
  · omega
  · omega
  · omega

/-- Moving one primitive step `(1,-1,-alpha,-beta)` preserves quotient
coordinates.  The hypotheses are written without truncated subtraction. -/
theorem rankThreeQuotientCoordinate_eq_of_primitive_step
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (h0 : f 0 = e 0 + 1)
    (h1 : e 1 = f 1 + 1)
    (h2 : e 2 = f 2 + alpha)
    (h3 : e 3 = f 3 + beta) :
    rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f := by
  rw [rankThreeQuotientCoordinate_eq_iff]
  omega

/-- Conversely, two quotient-equal exponents whose longitudinal coordinates
are `0` and `1` are exactly one primitive source step apart. -/
theorem primitive_pair_shape_of_quotient_eq_zero_one
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f)
    (he0 : e 0 = 0) (hf0 : f 0 = 1) :
    e 1 = f 1 + 1 ∧
      e 2 = f 2 + alpha ∧
      e 3 = f 3 + beta := by
  rw [rankThreeQuotientCoordinate_eq_iff] at hq
  rcases hq with ⟨hp, hr, hs⟩
  simp [he0, hf0] at hp hr hs
  omega

/-- Same statement with the endpoint orientation reversed. -/
theorem primitive_pair_shape_of_quotient_eq_one_zero
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f)
    (he0 : e 0 = 1) (hf0 : f 0 = 0) :
    f 1 = e 1 + 1 ∧
      f 2 = e 2 + alpha ∧
      f 3 = e 3 + beta := by
  have h := primitive_pair_shape_of_quotient_eq_zero_one
    alpha beta f e hq.symm hf0 he0
  exact h

/-- In a quotient fiber with longitudinal coordinate bounded by one, two
distinct exponents must occupy the two different longitudinal layers. -/
theorem zero_one_layers_of_quotient_eq_of_le_one
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f)
    (he : e 0 ≤ 1) (hf : f 0 ≤ 1) (hne : e ≠ f) :
    (e 0 = 0 ∧ f 0 = 1) ∨ (e 0 = 1 ∧ f 0 = 0) := by
  have hcoord : e 0 ≠ f 0 := by
    intro h0
    exact hne (eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
      alpha beta e f hq h0)
  interval_cases hE : e 0 <;> interval_cases hF : f 0 <;> simp_all

/-- Therefore every non-singleton fiber under the longitudinal bound has the
exact primitive two-layer shape. -/
theorem primitive_pair_shape_of_quotient_eq_of_le_one
    (alpha beta : ℕ) (e f : Fin 4 →₀ ℕ)
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f)
    (he : e 0 ≤ 1) (hf : f 0 ≤ 1) (hne : e ≠ f) :
    (e 0 = 0 ∧ f 0 = 1 ∧
      e 1 = f 1 + 1 ∧ e 2 = f 2 + alpha ∧ e 3 = f 3 + beta) ∨
    (e 0 = 1 ∧ f 0 = 0 ∧
      f 1 = e 1 + 1 ∧ f 2 = e 2 + alpha ∧ f 3 = e 3 + beta) := by
  rcases zero_one_layers_of_quotient_eq_of_le_one
      alpha beta e f hq he hf hne with h | h
  · left
    rcases h with ⟨he0, hf0⟩
    rcases primitive_pair_shape_of_quotient_eq_zero_one
      alpha beta e f hq he0 hf0 with ⟨h1, h2, h3⟩
    exact ⟨he0, hf0, h1, h2, h3⟩
  · right
    rcases h with ⟨he0, hf0⟩
    rcases primitive_pair_shape_of_quotient_eq_one_zero
      alpha beta e f hq he0 hf0 with ⟨h1, h2, h3⟩
    exact ⟨he0, hf0, h1, h2, h3⟩

/-- A finite bounded subset of one quotient fiber is exactly a two-point set as
soon as it contains two distinct exponents.  This is the combinatorial form
needed by the no-singleton carrier reconstruction. -/
theorem finset_eq_pair_of_rankThreeQuotientFiber_of_le_one
    (alpha beta : ℕ)
    (S : Finset (Fin 4 →₀ ℕ))
    (e f : Fin 4 →₀ ℕ)
    (he : e ∈ S) (hf : f ∈ S) (hne : e ≠ f)
    (hquot : ∀ g ∈ S,
      rankThreeQuotientCoordinate alpha beta g =
        rankThreeQuotientCoordinate alpha beta e)
    (hbound : ∀ g ∈ S, g 0 ≤ 1) :
    S = {e, f} := by
  have hqf := hquot f hf
  have hlayers := zero_one_layers_of_quotient_eq_of_le_one
    alpha beta e f hqf.symm (hbound e he) (hbound f hf) hne
  ext g
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hg
    have hqg := hquot g hg
    have hg0 : g 0 ≤ 1 := hbound g hg
    rcases hlayers with ⟨he0, hf0⟩ | ⟨he0, hf0⟩
    · by_cases hge : g 0 = e 0
      · left
        exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
          alpha beta g e hqg hge
      · right
        have hgf0 : g 0 = f 0 := by omega
        exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
          alpha beta g f (hqg.trans hqf.symm) hgf0
    · by_cases hge : g 0 = e 0
      · left
        exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
          alpha beta g e hqg hge
      · right
        have hgf0 : g 0 = f 0 := by omega
        exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
          alpha beta g f (hqg.trans hqf.symm) hgf0
  · intro hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf

end

end HC4.Polynomial
