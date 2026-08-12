import HC4.Valuation.AdaptiveAlignedSmithPositiveLongitudinalGap
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# First longitudinal departure at the final aligned Smith blocker

A positive longitudinal gap is enough to know that some later layer exists,
but the Schur/determinant machinery is organized by the *first* positive
order.  This file makes that order canonical.

For a fixed blocker exponent `e`, choose a nonzero coefficient at
longitudinal order `n`.  Among all positive offsets `r` for which the same
coefficient fibre has another nonzero coefficient at `n+r`, take the least
one using `Nat.find`.

The resulting certificate says

    coeff n       ≠ 0,
    coeff (n + q) ≠ 0,
    q > 0,

and every intermediate positive offset `0 < r < q` has zero coefficient.

This is a purely finite support statement.  It does not yet assert that the
same `q` is a Schur entry order; that identification is the next geometric
adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- A genuine first positive longitudinal departure in the coefficient fibre
over one exact Smith exponent.

The base order `n` need not itself be the first support exponent of the whole
fibre; what matters is that `q` is the first *later* nonzero offset from this
chosen occupied layer.
-/
def HasFirstExactSmithExponentLongitudinalDeparture
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent) : Prop :=
  ∃ n q : ℕ,
    0 < q ∧
    (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff n ≠ 0 ∧
    (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + q) ≠ 0 ∧
    ∀ r : ℕ,
      0 < r →
      r < q →
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + r) = 0

/-- Every positive same-exponent longitudinal gap contains a canonical first
later layer. -/
theorem HasExactSmithExponentPositiveLongitudinalGap.toFirstLongitudinalDeparture
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasExactSmithExponentPositiveLongitudinalGap F e) :
    HasFirstExactSmithExponentLongitudinalDeparture F e := by
  classical
  rcases h.coefficientFiber_two_nonzero with
    ⟨n, q, hq, hn, hnq⟩

  let A := longitudinalCoefficientPolynomial e.b e.c e.d F
  let p : ℕ → Prop :=
    fun r => 0 < r ∧ A.coeff (n + r) ≠ 0

  have hp : ∃ r : ℕ, p r := by
    refine ⟨q, hq, ?_⟩
    simpa [A] using hnq

  let q₀ : ℕ := Nat.find hp

  have hq₀spec : p q₀ :=
    Nat.find_spec hp

  refine ⟨n, q₀, hq₀spec.1, ?_, ?_, ?_⟩

  · simpa [A] using hn

  · simpa [A] using hq₀spec.2

  · intro r hrpos hrlt
    by_contra hrne
    have hpr : p r := by
      refine ⟨hrpos, ?_⟩
      simpa [A] using hrne
    exact (Nat.find_min hp hrlt) hpr

/-- The first departure certificate still gives two actual support monomials
over the same exact Smith exponent. -/
theorem HasFirstExactSmithExponentLongitudinalDeparture.support_pair
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasFirstExactSmithExponentLongitudinalDeparture F e) :
    ∃ n q : ℕ,
      0 < q ∧
      ((smithTransverseExponent e.b e.c e.d).cons n) ∈ F.support ∧
      ((smithTransverseExponent e.b e.c e.d).cons (n + q)) ∈ F.support := by
  rcases h with ⟨n, q, hq, hn, hnq, hbefore⟩

  have hdn :
      MvPolynomial.coeff
          ((smithTransverseExponent e.b e.c e.d).cons n) F ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hn

  have hdnq :
      MvPolynomial.coeff
          ((smithTransverseExponent e.b e.c e.d).cons (n + q)) F ≠ 0 := by
    rw [← coeff_longitudinalCoefficientPolynomial]
    exact hnq

  exact
    ⟨n, q, hq,
      MvPolynomial.mem_support_iff.mpr hdn,
      MvPolynomial.mem_support_iff.mpr hdnq⟩

/-- No source monomial over the same exact Smith exponent occurs at an
intermediate positive longitudinal offset. -/
theorem HasFirstExactSmithExponentLongitudinalDeparture.no_intermediate_support
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasFirstExactSmithExponentLongitudinalDeparture F e) :
    ∀ n q : ℕ,
      0 < q →
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff n ≠ 0 →
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + q) ≠ 0 →
      (∀ r : ℕ,
        0 < r →
        r < q →
        (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + r) = 0) →
      ∀ r : ℕ,
        0 < r →
        r < q →
        ((smithTransverseExponent e.b e.c e.d).cons (n + r)) ∉ F.support := by
  intro n q hq hn hnq hbefore r hrpos hrlt hrmem
  have hcoeff :
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + r) ≠ 0 := by
    rw [coeff_longitudinalCoefficientPolynomial]
    exact MvPolynomial.mem_support_iff.mp hrmem
  exact hcoeff (hbefore r hrpos hrlt)

/-- The first later layer has strictly larger ordinary source degree. -/
theorem HasFirstExactSmithExponentLongitudinalDeparture.ordinaryDegree_strict
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasFirstExactSmithExponentLongitudinalDeparture F e) :
    ∃ n q : ℕ,
      0 < q ∧
      HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent e.b e.c e.d).cons n) <
        HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent e.b e.c e.d).cons (n + q)) := by
  rcases h with ⟨n, q, hq, hn, hnq, hbefore⟩
  refine ⟨n, q, hq, ?_⟩
  rw [ordinaryDegree4_cons_smithTransverseExponent_eq,
      ordinaryDegree4_cons_smithTransverseExponent_eq]
  omega

section CharZero

variable [CharZero K]

/-- Strong final blocker first-departure interface.  There is no
surviving-shape escape on the canonical blocker path: the blocker's own
projected Smith exponent has a canonically minimal positive later layer. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.firstLongitudinalDeparture
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      B.exponent :=
  B.positiveLongitudinalGap.toFirstLongitudinalDeparture

/-- **Final blocker first-departure interface.**

Every canonical blocker is either already in the general surviving Smith
shape or has a canonically minimal positive longitudinal departure order over
its own unchanged projected Smith exponent.

The only missing step after this theorem is geometric: identify this first
longitudinal departure with the first nonzero relevant Schur numerator/order.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_firstLongitudinalDeparture
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        B.exponent := by
  rcases B.survivingShape_or_positiveLongitudinalGap with
    hsurviving | hgap
  · exact Or.inl hsurviving
  · exact Or.inr hgap.toFirstLongitudinalDeparture

end CharZero

end

end HC4.Valuation
