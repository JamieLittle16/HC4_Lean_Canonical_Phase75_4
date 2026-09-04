import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrParameterResidual
import Mathlib.Tactic

/-!
# A19.R18.21: finite `.pr` extremal scalar

At the highest longitudinal profile order the only longitudinal pairing is the
leading slice with itself.  Before doing any support selection inside that
slice, the weighted-Euler arithmetic can therefore be computed once for a
single source monomial.

If

* `n` is its longitudinal exponent,
* `t` is its total transverse degree,
* `q` is its honest contact-Rees parameter deficit,
* `r` is the integral contact slope, and
* `D = q + r*n + t` is the exact contact grading,

then the self contribution to the straightened raw complementary determinant
collapses to

    - n * t * (n + t - 1).

In particular all dependence on `q`, `r`, and `D` cancels.  This is the finite
coordinate identity needed to analyse the `qNN` layer without confusing the
contact and binary filtrations.
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

end

end HC4.Valuation
