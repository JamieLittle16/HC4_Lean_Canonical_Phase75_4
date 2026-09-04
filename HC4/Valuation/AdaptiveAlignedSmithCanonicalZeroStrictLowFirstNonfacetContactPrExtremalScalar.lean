import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrParameterResidual
import Mathlib.Tactic

/-!
# A19.R18.21: finite `.pr` extremal scalars

At the two exposed longitudinal profile orders the weighted-Euler arithmetic is
finite.  The highest order uses the leading slice with itself.  Once that
calculation forces the leading transverse degree to zero, the next order uses
the leading slice against the next-highest slice.

For one source monomial, if `n` is its longitudinal exponent, `t` its total
transverse degree, `q` its honest contact-Rees parameter deficit, `r` the
integral contact slope, and `D = q + r*n + t`, then the self contribution to
the straightened raw complementary determinant is

    - n * t * (n + t - 1).

For a pure-longitudinal leading monomial of longitudinal degree `N` and a
next-slice monomial of transverse degree `u`, the symmetric cross contribution
is

    N * u * (N - 1) * (u - 1).

Thus both contact deficits and the contact slope disappear from the two finite
coordinate calculations.  These identities are the arithmetic core needed to
analyse `qNN` and `qNM` without confusing the contact and binary filtrations.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **R18.21 PR extremal self scalar.**

The left side is exactly `x*z-y^2` for one contact monomial after the PR
weighted-Euler straightening, with `x = n(n-1)`,
`y = n(D-r-q)`, and the displayed falling-parameter expression for `z`.
The contact grading removes every auxiliary parameter and leaves only the
ordinary longitudinal/transverse degree factor on the right. -/
theorem prContactWeightedEuler_rawComplement_selfScalar
    (D r n t q : ℕ)
    (hgrade : q + r * n + t = D) :
    ((n : K) * ((n : K) - 1)) *
          ((D : K) * ((D : K) - 1) -
            2 * ((D : K) - 1) * (q : K) +
            (q : K) * ((q : K) - 1) +
            (r : K) * (1 - (r : K)) * (n : K)) -
        ((n : K) * ((D : K) - (r : K) - (q : K))) *
          ((n : K) * ((D : K) - (r : K) - (q : K))) =
      - (n : K) * (t : K) * ((n : K) + (t : K) - 1) := by
  have hgradeK :
      (D : K) = (q : K) + (r : K) * (n : K) + (t : K) := by
    exact_mod_cast hgrade.symm
  rw [hgradeK]
  ring

/-- **R18.21 PR next-extremal cross scalar.**

Assume the leading slice is already pure longitudinal.  If its longitudinal
exponent is `N`, its contact deficit is `qN`, and a next-slice monomial has
longitudinal exponent `M`, transverse degree `u`, and contact deficit `qM`,
then the symmetric `(N,M)+(M,N)` raw-complement contribution collapses to the
stated degree-only scalar. -/
theorem prContactWeightedEuler_rawComplement_crossScalar_of_topTransverseZero
    (D r N M u qN qM : ℕ)
    (htop : qN + r * N = D)
    (hnext : qM + r * M + u = D) :
    ((N : K) * ((N : K) - 1)) *
          ((D : K) * ((D : K) - 1) -
            2 * ((D : K) - 1) * (qM : K) +
            (qM : K) * ((qM : K) - 1) +
            (r : K) * (1 - (r : K)) * (M : K)) +
      ((M : K) * ((M : K) - 1)) *
          ((D : K) * ((D : K) - 1) -
            2 * ((D : K) - 1) * (qN : K) +
            (qN : K) * ((qN : K) - 1) +
            (r : K) * (1 - (r : K)) * (N : K)) -
      2 *
        ((N : K) * ((D : K) - (r : K) - (qN : K))) *
        ((M : K) * ((D : K) - (r : K) - (qM : K))) =
      (N : K) * (u : K) * ((N : K) - 1) * ((u : K) - 1) := by
  have htopK :
      (D : K) = (qN : K) + (r : K) * (N : K) := by
    exact_mod_cast htop.symm
  have hnextK :
      (D : K) = (qM : K) + (r : K) * (M : K) + (u : K) := by
    exact_mod_cast hnext.symm
  have hqMK :
      (qM : K) =
        (qN : K) + (r : K) * (N : K) -
          (r : K) * (M : K) - (u : K) := by
    linear_combination htopK - hnextK
  rw [htopK, hqMK]
  ring

end

end HC4.Valuation
