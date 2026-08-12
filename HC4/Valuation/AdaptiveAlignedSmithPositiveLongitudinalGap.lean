import HC4.Valuation.AdaptiveAlignedSmithExactExponentMixedBlocker
import Mathlib.Tactic

/-!
# Positive longitudinal gap at the final aligned Smith blocker

The preceding exact-exponent blocker theorem says that, unless the blocker
has already entered the general surviving Smith shape, the *same* projected
Smith exponent `e` supports two distinct longitudinal orders.

This file converts that unordered pair into the form needed by a genuine
departure clock:

    n  and  n + q,   with q > 0.

Nothing geometric is changed here.  The point is to isolate a positive
integer longitudinal order while keeping the transverse Smith exponent
definitionally fixed.  After this file the remaining blocker problem is no
longer a finite-support problem: it is to show that the determinant/Schur
clock must react to this positive stationary longitudinal gap.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- A positive later longitudinal layer over one *fixed* projected Smith
exponent.

The two source exponents differ only in coordinate `0`; their transverse
coordinates are definitionally those of `e`.
-/
def HasExactSmithExponentPositiveLongitudinalGap
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent) : Prop :=
  ∃ n q : ℕ,
    0 < q ∧
    ((smithTransverseExponent e.b e.c e.d).cons n) ∈ F.support ∧
    ((smithTransverseExponent e.b e.c e.d).cons (n + q)) ∈ F.support

/-- Exact same-exponent mixedness always contains an oriented positive
longitudinal gap. -/
theorem ExactSmithExponentMixedDegreeData.toPositiveLongitudinalGap
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : ExactSmithExponentMixedDegreeData F e) :
    HasExactSmithExponentPositiveLongitudinalGap F e := by
  rcases h with ⟨n₀, n₁, hne, hn₀, hn₁, _hdeg⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · let q := n₁ - n₀
    have hq : 0 < q := by
      dsimp [q]
      omega
    have hsum : n₀ + q = n₁ := by
      dsimp [q]
      omega
    refine ⟨n₀, q, hq, hn₀, ?_⟩
    simpa [hsum] using hn₁
  · let q := n₀ - n₁
    have hq : 0 < q := by
      dsimp [q]
      omega
    have hsum : n₁ + q = n₀ := by
      dsimp [q]
      omega
    refine ⟨n₁, q, hq, hn₁, ?_⟩
    simpa [hsum] using hn₀

/-- A positive longitudinal gap gives two actual nonzero coefficients in the
single univariate coefficient fibre over `e`. -/
theorem HasExactSmithExponentPositiveLongitudinalGap.coefficientFiber_two_nonzero
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasExactSmithExponentPositiveLongitudinalGap F e) :
    ∃ n q : ℕ,
      0 < q ∧
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff n ≠ 0 ∧
      (longitudinalCoefficientPolynomial e.b e.c e.d F).coeff (n + q) ≠ 0 := by
  rcases h with ⟨n, q, hq, hn, hnq⟩
  have hcn :
      MvPolynomial.coeff
          ((smithTransverseExponent e.b e.c e.d).cons n) F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hn
  have hcnq :
      MvPolynomial.coeff
          ((smithTransverseExponent e.b e.c e.d).cons (n + q)) F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hnq
  refine ⟨n, q, hq, ?_, ?_⟩
  · rw [coeff_longitudinalCoefficientPolynomial]
    exact hcn
  · rw [coeff_longitudinalCoefficientPolynomial]
    exact hcnq

/-- In particular the exact coefficient fibre over `e` is nonzero. -/
theorem HasExactSmithExponentPositiveLongitudinalGap.coefficientFiber_ne_zero
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasExactSmithExponentPositiveLongitudinalGap F e) :
    longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 := by
  rcases h.coefficientFiber_two_nonzero with
    ⟨n, q, hq, hn, hnq⟩
  intro hzero
  rw [hzero] at hn
  simp at hn

/-- The exact coefficient fibre over `e` cannot be a single monomial. -/
theorem HasExactSmithExponentPositiveLongitudinalGap.coefficientFiber_not_monomial
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasExactSmithExponentPositiveLongitudinalGap F e) :
    ∀ m : ℕ, ∀ a : K, a ≠ 0 →
      longitudinalCoefficientPolynomial e.b e.c e.d F ≠
        Polynomial.monomial m a := by
  rcases h.coefficientFiber_two_nonzero with
    ⟨n, q, hq, hn, hnq⟩
  intro m a ha hmono
  have hneq : n ≠ n + q := by omega
  by_cases hmn : m = n
  · subst m
    have hz :
        (Polynomial.monomial n a).coeff (n + q) = 0 := by
      exact Polynomial.coeff_monomial_of_ne a (Ne.symm hneq)
    rw [hmono] at hnq
    exact hnq hz
  · have hz :
        (Polynomial.monomial m a).coeff n = 0 := by
      exact Polynomial.coeff_monomial_of_ne a (Ne.symm hmn)
    rw [hmono] at hn
    exact hn hz

/-- The two layers really have distinct ordinary source degrees; the
difference is exactly the positive longitudinal gap. -/
theorem HasExactSmithExponentPositiveLongitudinalGap.ordinaryDegree_strict
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasExactSmithExponentPositiveLongitudinalGap F e) :
    ∃ n q : ℕ,
      0 < q ∧
      HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent e.b e.c e.d).cons n) <
        HC4.Polynomial.ordinaryDegree4
          ((smithTransverseExponent e.b e.c e.d).cons (n + q)) := by
  rcases h with ⟨n, q, hq, hn, hnq⟩
  refine ⟨n, q, hq, ?_⟩
  rw [ordinaryDegree4_cons_smithTransverseExponent_eq,
      ordinaryDegree4_cons_smithTransverseExponent_eq]
  omega

section CharZero

variable [CharZero K]

/-- Strong stationary blocker departure interface.  Every canonical
blocker carries a positive later longitudinal layer over its own unchanged
projected Smith exponent. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.positiveLongitudinalGap
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasExactSmithExponentPositiveLongitudinalGap
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      B.exponent :=
  B.exactExponentMixedDegree.toPositiveLongitudinalGap

/-- **Stationary blocker departure interface.**

Every canonical blocker is either already in the general surviving Smith
shape or carries a genuinely positive later longitudinal layer over its own
unchanged projected Smith exponent.

This is the interface the determinant/Schur forcing theorem should consume.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_positiveLongitudinalGap
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      HasExactSmithExponentPositiveLongitudinalGap
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        B.exponent := by
  rcases B.survivingShape_or_exactExponentMixedDegree with
    hsurviving | hmixed
  · exact Or.inl hsurviving
  · exact Or.inr hmixed.toPositiveLongitudinalGap

end CharZero

end

end HC4.Valuation
