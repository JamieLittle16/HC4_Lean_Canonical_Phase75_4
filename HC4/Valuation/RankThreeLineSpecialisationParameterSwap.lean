import HC4.Valuation.ActualParameterLayer
import HC4.Polynomial.RankThreeMvSubstitution
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-!
# Swap parameter and longitudinal variables after rank-three specialisation

A polynomial-parameter source family has coefficient ring `K[τ]`.  Applying
the rank-three line specialisation produces a nested polynomial

    K[τ][X],

with longitudinal variable `X` outside and family parameter `τ` inside.
Mathlib's `Polynomial.Bivariate.swap` exchanges these variables, yielding

    K[X][τ].

After this swap, extracting outer coefficient `q` is exactly the rank-three
line specialisation of the honest parameter layer `familyParameterLayer P q`.
This file records that representation bridge once.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open scoped Polynomial.Bivariate

universe u
variable {K : Type u} [Field K]

/-- Exact parameter-layer extraction is additive. -/
theorem familyParameterLayer_add
    (P Q : MvPolynomial (Fin 4) (Polynomial K)) (q : ℕ) :
    familyParameterLayer (P + Q) q =
      familyParameterLayer P q + familyParameterLayer Q q := by
  apply MvPolynomial.ext
  intro d
  simp [familyParameterLayer_coeff]

/-- Exact parameter layer of a single multivariate monomial. -/
theorem familyParameterLayer_monomial
    (d : Fin 4 →₀ ℕ) (c : Polynomial K) (q : ℕ) :
    familyParameterLayer (MvPolynomial.monomial d c) q =
      MvPolynomial.monomial d (c.coeff q) := by
  apply MvPolynomial.ext
  intro e
  rw [familyParameterLayer_coeff]
  by_cases hed : e = d
  · subst e
    simp
  · simp [MvPolynomial.coeff_monomial, hed]

/-- **Parameter/longitudinal swap coefficient bridge.**

After line-specialising a polynomial-parameter source and swapping the two
univariate variables, the coefficient at parameter order `q` is literally the
line specialisation of `familyParameterLayer P q`. -/
theorem coeff_swap_rankThreeLineSpecialisation_eq_parameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K)) (q : ℕ) :
    (Polynomial.Bivariate.swap
      (rankThreeLineSpecialisation P)).coeff q =
        rankThreeLineSpecialisation (familyParameterLayer P q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, map_add, Polynomial.coeff_add, familyParameterLayer_add]
      rw [map_add, hP, hQ]
  | monomial d c =>
      rw [familyParameterLayer_monomial]
      simp [rankThreeLineSpecialisation,
        Polynomial.Bivariate.swap_monomial,
        Polynomial.Bivariate.swap_C]

end

end HC4.Valuation
