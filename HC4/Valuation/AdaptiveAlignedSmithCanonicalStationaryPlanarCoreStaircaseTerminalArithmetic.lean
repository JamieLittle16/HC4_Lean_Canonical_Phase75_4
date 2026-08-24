import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseRecurrence
import Mathlib.Tactic

/-!
# Terminal arithmetic for the stationary binary staircase

The all-depth recurrence isolates an arithmetic ray of ordinary degrees

    D, D-delta, D-2*delta, ...

whose top transverse jets have orders

    0, 1, 2, ... .

After straightening the locked linear form, the top diagonal therefore has
formal shape

    x^D h(y / x^r),    r = delta + 1.

For the binary Hessian equation, direct differentiation gives the scalar
profile equation

    D(D-1) h h'' - (D-r)^2 (h')^2
      - r(r-1) z h' h'' = 0.

This file records the two coefficient factorizations which make finite
termination impossible.

* At the highest nonzero profile coefficient `N`, the coefficient of
  `z^(2N-2)` factors as

      -N (Nr-D) (Nr-D-N+1).

  Polynomial support gives `Nr <= D`.  For `N >= 2`, the second factor
  cannot vanish, so one is forced onto the boundary `D = Nr`.

* If `M < N` is the next-highest nonzero profile index, the coefficient of
  `z^(N+M-2)` then factors as

      Nr (M-N) (N-1) (Mr-Nr+1).

  Every factor is nonzero when `r >= 2`.  Equivalently the missing-degree
  gap would have to satisfy `(N-M)r = 1`, impossible for a positive gap and
  `r >= 2`.

This is the scalar terminal obstruction behind the stationary staircase.
The next file only has to extract these two scalar equations from the exact
transverse jets already carried by the Lean frontier.
-/

namespace HC4.Valuation

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Universal profile coefficient scalars -/

/-- Raw coefficient multiplying the square of the highest profile
coefficient in the binary Hessian profile equation. -/
def binaryStaircaseProfileLeadingScalar
    (D r N : ℕ) : K :=
  (D : K) * ((D : K) - 1) * (N : K) * ((N : K) - 1) -
    (((D : K) - (r : K)) ^ 2) * ((N : K) ^ 2) -
    (r : K) * ((r : K) - 1) * ((N : K) ^ 2) * ((N : K) - 1)

/-- Bilinear coefficient multiplying the product of two distinct profile
coefficients at indices `N` and `M`. -/
def binaryStaircaseProfileCrossScalar
    (D r N M : ℕ) : K :=
  (D : K) * ((D : K) - 1) *
      ((N : K) * ((N : K) - 1) + (M : K) * ((M : K) - 1)) -
    2 * (((D : K) - (r : K)) ^ 2) * (N : K) * (M : K) -
    (r : K) * ((r : K) - 1) * (N : K) * (M : K) *
      ((N : K) + (M : K) - 2)

/-- Exact factorisation of the highest-profile Hessian coefficient. -/
theorem binaryStaircaseProfileLeadingScalar_factor
    (D r N : ℕ) :
    binaryStaircaseProfileLeadingScalar (K := K) D r N =
      -(N : K) *
        (((N : K) * (r : K) - (D : K)) *
          ((N : K) * (r : K) - (D : K) - (N : K) + 1)) := by
  unfold binaryStaircaseProfileLeadingScalar
  ring

/-- Once the highest support exponent lies exactly on the polynomial boundary
`D = N*r`, the next-highest bilinear coefficient has the displayed simple
factorisation. -/
theorem binaryStaircaseProfileCrossScalar_factor_of_boundary
    (r N M : ℕ) :
    binaryStaircaseProfileCrossScalar (K := K) (N * r) r N M =
      (N : K) * (r : K) * ((M : K) - (N : K)) * ((N : K) - 1) *
        ((M : K) * (r : K) - (N : K) * (r : K) + 1) := by
  unfold binaryStaircaseProfileCrossScalar
  push_cast
  ring

/-! ## Arithmetic nonvanishing -/

/-- Under polynomial support `N*r <= D`, the second root of the leading
factorisation is impossible as soon as `N >= 2`. -/
theorem binaryStaircaseProfile_secondLeadingFactor_ne_zero
    (D r N : ℕ)
    (hN : 2 ≤ N)
    (hsupport : N * r ≤ D) :
    (N : K) * (r : K) - (D : K) - (N : K) + 1 ≠ 0 := by
  intro hzero
  have heqK :
      (D : K) = (N : K) * (r : K) - (N : K) + 1 := by
    linear_combination -hzero
  have heqZ :
      (D : ℤ) = (N : ℤ) * (r : ℤ) - (N : ℤ) + 1 := by
    exact_mod_cast heqK
  have hsupportZ :
      (N : ℤ) * (r : ℤ) ≤ (D : ℤ) := by
    exact_mod_cast hsupport
  omega

/-- Therefore vanishing of the leading profile coefficient forces the highest
profile monomial onto the exact support boundary `D = N*r`. -/
theorem binaryStaircaseProfile_boundary_of_leadingScalar_eq_zero
    (D r N : ℕ)
    (hN : 2 ≤ N)
    (hsupport : N * r ≤ D)
    (hlead : binaryStaircaseProfileLeadingScalar (K := K) D r N = 0) :
    D = N * r := by
  rw [binaryStaircaseProfileLeadingScalar_factor] at hlead
  rcases mul_eq_zero.mp hlead with hNzero | hrest
  · have hNcast : (N : K) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    exact ((neg_ne_zero.mpr hNcast) hNzero).elim
  · rcases mul_eq_zero.mp hrest with hboundary | hsecond
    · have hEqK : (N : K) * (r : K) = (D : K) := sub_eq_zero.mp hboundary
      exact_mod_cast hEqK.symm
    · exact (binaryStaircaseProfile_secondLeadingFactor_ne_zero
        (K := K) D r N hN hsupport hsecond).elim

/-- A positive integral gap times a transverse weight at least two cannot be
one.  This is the integer content of the fractional terminal exponent. -/
theorem binaryStaircaseProfile_gap_mul_ne_one
    (r N M : ℕ)
    (hr : 2 ≤ r)
    (hMN : M < N) :
    (N - M) * r ≠ 1 := by
  have hgap : 1 ≤ N - M := by omega
  have htwo : 2 ≤ (N - M) * r := by
    have hmul := Nat.mul_le_mul hgap hr
    simpa using hmul
  omega

/-- The last factor in the next-highest profile coefficient is nonzero. -/
theorem binaryStaircaseProfile_lastCrossFactor_ne_zero
    (r N M : ℕ)
    (hr : 2 ≤ r)
    (hMN : M < N) :
    (M : K) * (r : K) - (N : K) * (r : K) + 1 ≠ 0 := by
  intro hzero
  have hle : M ≤ N := Nat.le_of_lt hMN
  have heqK : (((N - M) * r : ℕ) : K) = 1 := by
    rw [Nat.cast_mul, Nat.cast_sub hle]
    linear_combination -hzero
  have heqNat : (N - M) * r = 1 := by
    exact_mod_cast heqK
  exact binaryStaircaseProfile_gap_mul_ne_one r N M hr hMN heqNat

/-- The complete next-highest bilinear coefficient is nonzero at the support
boundary. -/
theorem binaryStaircaseProfileCrossScalar_ne_zero_of_boundary
    (r N M : ℕ)
    (hr : 2 ≤ r)
    (hN : 2 ≤ N)
    (hMN : M < N) :
    binaryStaircaseProfileCrossScalar (K := K) (N * r) r N M ≠ 0 := by
  rw [binaryStaircaseProfileCrossScalar_factor_of_boundary]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact_mod_cast (show N ≠ 0 by omega)
        · exact_mod_cast (show r ≠ 0 by omega)
      · apply sub_ne_zero.mpr
        intro hEq
        have hmn : M = N := by exact_mod_cast hEq
        omega
    · have hNm1 : ((N : K) - 1) ≠ 0 := by
        intro hzero
        have hEqK : (N : K) = 1 := sub_eq_zero.mp hzero
        have hEqNat : N = 1 := by exact_mod_cast hEqK
        omega
      exact hNm1
  · exact binaryStaircaseProfile_lastCrossFactor_ne_zero
      (K := K) r N M hr hMN

/-! ## Packaged finite-profile contradiction -/

/-- **Finite staircase terminal contradiction, scalar form.**

Suppose `N >= 2` is the highest nonzero top-diagonal profile index and
`M < N` is the next-highest nonzero index.  Polynomial support says
`N*r <= D`, with `r >= 2`.  If the Hessian profile equation supplies its
highest and next-highest scalar equations, then no such finite profile can
exist.

The amplitudes are retained explicitly because this is the exact interface
produced by coefficient extraction from the Lean staircase. -/
theorem binaryFiniteStaircaseProfile_terminal_impossible
    (D r N M : ℕ)
    (hr : 2 ≤ r)
    (hN : 2 ≤ N)
    (hMN : M < N)
    (hsupport : N * r ≤ D)
    (aN aM : K)
    (haN : aN ≠ 0)
    (haM : aM ≠ 0)
    (hleadingEq :
      aN ^ 2 * binaryStaircaseProfileLeadingScalar (K := K) D r N = 0)
    (hcrossEq :
      aN * aM * binaryStaircaseProfileCrossScalar (K := K) D r N M = 0) :
    False := by
  have hleadingScalar :
      binaryStaircaseProfileLeadingScalar (K := K) D r N = 0 := by
    apply (mul_eq_zero.mp hleadingEq).resolve_left
    exact pow_ne_zero 2 haN
  have hboundary : D = N * r :=
    binaryStaircaseProfile_boundary_of_leadingScalar_eq_zero
      (K := K) D r N hN hsupport hleadingScalar
  have hcrossScalar :
      binaryStaircaseProfileCrossScalar (K := K) D r N M = 0 := by
    rcases mul_eq_zero.mp hcrossEq with hprod | hscalar
    · rcases mul_eq_zero.mp hprod with hNa | hMa
      · exact (haN hNa).elim
      · exact (haM hMa).elim
    · exact hscalar
  subst D
  exact (binaryStaircaseProfileCrossScalar_ne_zero_of_boundary
    (K := K) r N M hr hN hMN) hcrossScalar

/-- HC4 staircase specialization: the transverse profile weight is
`r = delta + 1`, automatically at least two for a positive degree gap. -/
theorem binaryFiniteStaircaseProfile_terminal_impossible_of_positiveGap
    (D delta N M : ℕ)
    (hdelta : 0 < delta)
    (hN : 2 ≤ N)
    (hMN : M < N)
    (hsupport : N * (delta + 1) ≤ D)
    (aN aM : K)
    (haN : aN ≠ 0)
    (haM : aM ≠ 0)
    (hleadingEq :
      aN ^ 2 *
        binaryStaircaseProfileLeadingScalar (K := K) D (delta + 1) N = 0)
    (hcrossEq :
      aN * aM *
        binaryStaircaseProfileCrossScalar (K := K) D (delta + 1) N M = 0) :
    False := by
  exact binaryFiniteStaircaseProfile_terminal_impossible
    (K := K)
    (D := D) (r := delta + 1) (N := N) (M := M)
    (hr := by omega)
    (hN := hN) (hMN := hMN) (hsupport := hsupport)
    (aN := aN) (aM := aM)
    (haN := haN) (haM := haM)
    (hleadingEq := hleadingEq) (hcrossEq := hcrossEq)

end

end HC4.Valuation
