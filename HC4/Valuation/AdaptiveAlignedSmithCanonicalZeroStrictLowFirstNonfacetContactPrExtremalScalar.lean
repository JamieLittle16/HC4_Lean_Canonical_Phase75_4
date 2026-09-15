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

/-! ## Zero-forcing consequences used by the closing extremal argument -/

/-- If the PR self scalar vanishes at a genuinely positive longitudinal
exponent, the monomial is forced to be pure longitudinal.  This is the exact
finite arithmetic implication needed at the first exposed order; it uses only
characteristic zero and no Schur or support hypothesis. -/
theorem prContactWeightedEuler_selfDegreeScalar_eq_zero_forces_transverse_zero
    (n t : ℕ)
    (hn : 0 < n)
    (hzero :
      - (n : K) * (t : K) * ((n : K) + (t : K) - 1) = 0) :
    t = 0 := by
  by_contra ht
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  have hn0 : (n : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have ht0 : (t : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt htpos)
  have hlast : (n : K) + (t : K) - 1 ≠ 0 := by
    intro hz
    have hone : (n : K) + (t : K) = 1 := by
      linear_combination hz
    have hnat : n + t = 1 := by
      exact_mod_cast hone
    omega
  exact
    (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn0) ht0) hlast) hzero

/-- After the leading slice has become pure longitudinal, vanishing of the PR
cross scalar at longitudinal degree `N ≥ 2` forces the next transverse degree
to be one of the two finite possibilities `0` or `1`.  This is deliberately
weaker than choosing either branch: the next geometric commit must rule out
the surviving alternative from the actual terminal equations. -/
theorem prContactWeightedEuler_crossDegreeScalar_eq_zero_forces_transverse_zero_or_one
    (N u : ℕ)
    (hN : 2 ≤ N)
    (hzero :
      (N : K) * (u : K) * ((N : K) - 1) * ((u : K) - 1) = 0) :
    u = 0 ∨ u = 1 := by
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  by_cases hu1 : u = 1
  · exact Or.inr hu1
  exfalso
  have hNpos : 0 < N := by omega
  have hN0 : (N : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNpos)
  have hu0K : (u : K) ≠ 0 := by
    exact_mod_cast hu0
  have hNm1 : (N : K) - 1 ≠ 0 := by
    intro hz
    have hone : (N : K) = 1 := by
      linear_combination hz
    have hNat : N = 1 := by
      exact_mod_cast hone
    omega
  have hum1 : (u : K) - 1 ≠ 0 := by
    intro hz
    have hone : (u : K) = 1 := by
      linear_combination hz
    have hNat : u = 1 := by
      exact_mod_cast hone
    exact hu1 hNat
  exact
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 hu0K) hNm1) hum1) hzero

end

end HC4.Valuation
