import HC4.Polynomial.RankThreeVerticalLine
import HC4.Newton.SmithRefinedFacePolynomial
import HC4.Newton.MixedDegreeAxisCollision
import Mathlib.Tactic

/-!
# A18.5.13: an exact Smith fibre is the honest vertical rank-three line

The Smith projection forgets source coordinate `0`.  Therefore restricting an
actual four-variable polynomial to one singleton Smith exponent
`e = (b,c,d)` should do nothing more mysterious than retain the univariate
longitudinal coefficient fibre over `(b,c,d)`.

A18.5.10 introduced the honest multivariate realisation of precisely such a
fibre:

    rankThreeVerticalPolynomial b c d φ
      = x₁^b x₂^c x₃^d φ(x₀).

This file proves the two descriptions are literally equal.  It is the missing
representation adapter needed to feed existing Smith-face geometry into the
vertical rank-three moment theorem without reconstructing coefficients or
introducing Laurent monomials.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K]

/-- Exact coefficient formula for the honest vertical-line polynomial. -/
theorem coeff_rankThreeVerticalPolynomial
    (b c d : ℕ)
    (phi : Polynomial K)
    (q : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff q
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) =
      if q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
      then phi.coeff (q (0 : Fin 4))
      else 0 := by
  classical
  unfold HC4.Polynomial.rankThreeVerticalPolynomial
  rw [Polynomial.sum_def]
  simp only [MvPolynomial.coeff_sum]
  by_cases htrans :
      q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
  · rw [if_pos htrans]
    let j := q (0 : Fin 4)
    have hq :
        q = HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d j := by
      ext i
      fin_cases i <;>
        simp [j, HC4.Polynomial.rankThreeVerticalExponentFinsupp,
          htrans.1, htrans.2.1, htrans.2.2]
    by_cases hj : j ∈ phi.support
    · rw [Finset.sum_eq_single j]
      · rw [HC4.Polynomial.rankThreeVerticalTerm_eq_monomial]
        rw [hq, MvPolynomial.coeff_monomial]
        simp
      · intro k hk hkj
        rw [HC4.Polynomial.rankThreeVerticalTerm_eq_monomial]
        rw [MvPolynomial.coeff_monomial]
        have hne :
            HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d k ≠ q := by
          intro heq
          have h0 := congrArg (fun z : Fin 4 →₀ ℕ => z (0 : Fin 4)) heq
          rw [hq] at h0
          simp [HC4.Polynomial.rankThreeVerticalExponentFinsupp] at h0
          exact hkj h0
        simp [hne]
      · intro hnot
        exact (hnot hj).elim
    · have hj0 : phi.coeff j = 0 :=
        Polynomial.notMem_support_iff.mp hj
      rw [show q (0 : Fin 4) = j by rfl, hj0]
      apply Finset.sum_eq_zero
      intro k hk
      rw [HC4.Polynomial.rankThreeVerticalTerm_eq_monomial]
      rw [MvPolynomial.coeff_monomial]
      have hne :
          HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d k ≠ q := by
        intro heq
        have h0 := congrArg (fun z : Fin 4 →₀ ℕ => z (0 : Fin 4)) heq
        have hkj : k = j := by
          simpa [j, HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h0
        subst k
        exact hj hk
      simp [hne]
  · rw [if_neg htrans]
    apply Finset.sum_eq_zero
    intro k hk
    rw [HC4.Polynomial.rankThreeVerticalTerm_eq_monomial]
    rw [MvPolynomial.coeff_monomial]
    have hne :
        HC4.Polynomial.rankThreeVerticalExponentFinsupp b c d k ≠ q := by
      intro heq
      apply htrans
      have h1 := congrArg (fun z : Fin 4 →₀ ℕ => z (1 : Fin 4)) heq
      have h2 := congrArg (fun z : Fin 4 →₀ ℕ => z (2 : Fin 4)) heq
      have h3 := congrArg (fun z : Fin 4 →₀ ℕ => z (3 : Fin 4)) heq
      constructor
      · simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h1.symm
      · constructor
        · simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h2.symm
        · simpa [HC4.Polynomial.rankThreeVerticalExponentFinsupp] using h3.symm
    simp [hne]

/-- **Singleton Smith restriction = honest vertical line.**
Filtering `F` to one exact Smith exponent `(b,c,d)` is literally the
multivariate realisation of its longitudinal coefficient polynomial. -/
theorem smithSubfacePolynomial_singleton_eq_rankThreeVerticalPolynomial
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent) :
    smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F =
      HC4.Polynomial.rankThreeVerticalPolynomial
        e.b e.c e.d
        (longitudinalCoefficientPolynomial e.b e.c e.d F) := by
  classical
  rcases e with ⟨b, c, d⟩
  apply MvPolynomial.ext
  intro q
  rw [coeff_smithSubfacePolynomial]
  rw [coeff_rankThreeVerticalPolynomial]
  by_cases htrans :
      q (1 : Fin 4) = b ∧ q (2 : Fin 4) = c ∧ q (3 : Fin 4) = d
  · have hproj :
        smithSupportExponentOf (1 : Fin 4) 2 3 q =
          ({ b := b, c := c, d := d } : SmithSupportExponent) := by
      simp [smithSupportExponentOf,
        htrans.1, htrans.2.1, htrans.2.2]
    rw [if_pos htrans]
    simp [hproj]
    rw [coeff_longitudinalCoefficientPolynomial]
    have hq :
        ((smithTransverseExponent b c d).cons (q (0 : Fin 4))) = q := by
      apply Finsupp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · rw [Finsupp.cons_succ]
        fin_cases j
        · simpa [smithTransverseExponent] using htrans.1.symm
        · simpa [smithTransverseExponent] using htrans.2.1.symm
        · simpa [smithTransverseExponent] using htrans.2.2.symm
    rw [hq]
  · have hproj :
        smithSupportExponentOf (1 : Fin 4) 2 3 q ≠
          ({ b := b, c := c, d := d } : SmithSupportExponent) := by
      intro heq
      apply htrans
      have hb := congrArg SmithSupportExponent.b heq
      have hc := congrArg SmithSupportExponent.c heq
      have hd := congrArg SmithSupportExponent.d heq
      exact ⟨by simpa using hb, by simpa using hc, by simpa using hd⟩
    rw [if_neg htrans]
    simp [hproj]

end

end HC4.Valuation