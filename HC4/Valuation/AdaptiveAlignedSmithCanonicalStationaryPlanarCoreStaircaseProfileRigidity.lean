import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseTerminalArithmetic
import HC4.Polynomial.AutonomousODEQuadraticRigidity
import Mathlib.Tactic

/-!
# Polynomial rigidity of the stationary binary staircase profile

The terminal-arithmetic file proves that a finite staircase profile cannot
have a highest nonzero coefficient `N >= 2` together with a next-highest
coefficient `M < N` once the two exposed Hessian coefficient equations are
known.

This file performs that coefficient extraction once and for all directly for
a one-variable polynomial profile.

For a profile `h(z)` set

    E h = z h',
    F h = z^2 h'' = E(E h) - E h.

The stationary binary Hessian equation, after multiplication by `z^2`, is

    D(D-1) h (F h)
      - (D-r)^2 (E h)^2
      - r(r-1) (E h) (F h) = 0.

The Euler form is particularly convenient in Lean: both `E` and `F` preserve
ordinary polynomial degree, and their coefficient actions are simply

    [z^n] E h = n a_n,
    [z^n] F h = n(n-1) a_n.

Hence the coefficient at `2N` is exactly the leading scalar from the previous
file.  Removing the leading monomial leaves a nonzero polynomial `q` because
the profile has nonzero constant term.  If `M = natDegree q`, the coefficient
at `N+M` is exactly the next-highest cross scalar: the pure leading piece has
support only at `2N`, while the pure remainder has degree at most `2M`.

Consequently every polynomial profile with nonzero constant term, support
bound `natDegree h * r ≤ D`, `r >= 2`, and zero stationary profile residual
has degree at most one.

The next stationary-core file therefore only has to straighten the actual
binary staircase into this one-variable profile.  No further all-depth
coefficient induction is needed.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ## Euler form of the profile equation -/

/-- Falling second Euler operator `z^2 d^2/dz^2`.  Writing it as
`E(E h) - E h` avoids all predecessor arithmetic at coefficients `0` and `1`. -/
def binaryStaircaseProfileSecondEuler
    (h : Polynomial K) : Polynomial K :=
  eulerDerivative (eulerDerivative h) - eulerDerivative h

/-- Coefficient action of the falling second Euler operator. -/
@[simp]
theorem coeff_binaryStaircaseProfileSecondEuler
    (h : Polynomial K) (n : ℕ) :
    (binaryStaircaseProfileSecondEuler h).coeff n =
      (n : K) * ((n : K) - 1) * h.coeff n := by
  unfold binaryStaircaseProfileSecondEuler
  simp only [Polynomial.coeff_sub, coeff_eulerDerivative]
  ring

/-- The falling second Euler operator does not increase degree. -/
theorem natDegree_binaryStaircaseProfileSecondEuler_le
    (h : Polynomial K) :
    (binaryStaircaseProfileSecondEuler h).natDegree ≤ h.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_binaryStaircaseProfileSecondEuler]
  have hz : h.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [hz]

/-- Euler differentiation is additive. -/
theorem eulerDerivative_add_profile
    (p q : Polynomial K) :
    eulerDerivative (p + q) = eulerDerivative p + eulerDerivative q := by
  simp [eulerDerivative, Polynomial.derivative_add, mul_add]

/-- The falling second Euler operator is additive. -/
theorem binaryStaircaseProfileSecondEuler_add
    (p q : Polynomial K) :
    binaryStaircaseProfileSecondEuler (p + q) =
      binaryStaircaseProfileSecondEuler p +
        binaryStaircaseProfileSecondEuler q := by
  unfold binaryStaircaseProfileSecondEuler
  simp only [eulerDerivative_add_profile]
  ring

/-- Polynomial residual of the stationary one-variable staircase equation,
after multiplication by `z^2`. -/
def binaryStaircaseProfileResidual
    (D r : ℕ) (h : Polynomial K) : Polynomial K :=
  Polynomial.C ((D : K) * ((D : K) - 1)) *
      (h * binaryStaircaseProfileSecondEuler h) -
    Polynomial.C (((D : K) - (r : K)) ^ 2) *
      (eulerDerivative h * eulerDerivative h) -
    Polynomial.C ((r : K) * ((r : K) - 1)) *
      (eulerDerivative h * binaryStaircaseProfileSecondEuler h)

/-- Bilinear polarization of the quadratic profile residual.  The factors are
ordered so that the degree-`N` polynomial always appears on the left of the
degree-`M` polynomial; this makes exact top-coefficient extraction direct. -/
def binaryStaircaseProfileCross
    (D r : ℕ) (p q : Polynomial K) : Polynomial K :=
  Polynomial.C ((D : K) * ((D : K) - 1)) *
      (p * binaryStaircaseProfileSecondEuler q +
        binaryStaircaseProfileSecondEuler p * q) -
    Polynomial.C (((D : K) - (r : K)) ^ 2) *
      (eulerDerivative p * eulerDerivative q +
        eulerDerivative p * eulerDerivative q) -
    Polynomial.C ((r : K) * ((r : K) - 1)) *
      (eulerDerivative p * binaryStaircaseProfileSecondEuler q +
        binaryStaircaseProfileSecondEuler p * eulerDerivative q)

/-- Quadratic polarization identity for the profile residual. -/
theorem binaryStaircaseProfileResidual_add
    (D r : ℕ) (p q : Polynomial K) :
    binaryStaircaseProfileResidual D r (p + q) =
      binaryStaircaseProfileResidual D r p +
        binaryStaircaseProfileCross D r p q +
          binaryStaircaseProfileResidual D r q := by
  unfold binaryStaircaseProfileResidual binaryStaircaseProfileCross
  simp only [eulerDerivative_add_profile,
    binaryStaircaseProfileSecondEuler_add]
  ring

/-! ## Exact exposed coefficients -/

/-- The coefficient at twice an upper degree bound is the square of the top
coefficient times the universal leading staircase scalar. -/
theorem coeff_add_self_binaryStaircaseProfileResidual
    (D r N : ℕ)
    (h : Polynomial K)
    (hdeg : h.natDegree ≤ N) :
    (binaryStaircaseProfileResidual D r h).coeff (N + N) =
      (h.coeff N) ^ 2 *
        binaryStaircaseProfileLeadingScalar (K := K) D r N := by
  have hE : (eulerDerivative h).natDegree ≤ N :=
    le_trans (natDegree_eulerDerivative_le h) hdeg
  have hF : (binaryStaircaseProfileSecondEuler h).natDegree ≤ N :=
    le_trans (natDegree_binaryStaircaseProfileSecondEuler_le h) hdeg
  unfold binaryStaircaseProfileResidual
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hdeg hF]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hE hE]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hE hF]
  simp only [coeff_eulerDerivative, coeff_binaryStaircaseProfileSecondEuler]
  unfold binaryStaircaseProfileLeadingScalar
  ring

/-- The coefficient at the sum of two degree bounds in the polarized
residual is exactly the product of the two top coefficients times the
universal cross scalar. -/
theorem coeff_add_binaryStaircaseProfileCross
    (D r N M : ℕ)
    (p q : Polynomial K)
    (hp : p.natDegree ≤ N)
    (hq : q.natDegree ≤ M) :
    (binaryStaircaseProfileCross D r p q).coeff (N + M) =
      p.coeff N * q.coeff M *
        binaryStaircaseProfileCrossScalar (K := K) D r N M := by
  have hpE : (eulerDerivative p).natDegree ≤ N :=
    le_trans (natDegree_eulerDerivative_le p) hp
  have hqE : (eulerDerivative q).natDegree ≤ M :=
    le_trans (natDegree_eulerDerivative_le q) hq
  have hpF : (binaryStaircaseProfileSecondEuler p).natDegree ≤ N :=
    le_trans (natDegree_binaryStaircaseProfileSecondEuler_le p) hp
  have hqF : (binaryStaircaseProfileSecondEuler q).natDegree ≤ M :=
    le_trans (natDegree_binaryStaircaseProfileSecondEuler_le q) hq
  unfold binaryStaircaseProfileCross
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp hqF]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpF hq]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpE hqE]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpE hqF]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpF hqE]
  simp only [coeff_eulerDerivative, coeff_binaryStaircaseProfileSecondEuler]
  unfold binaryStaircaseProfileCrossScalar
  ring

/-- Above twice an upper degree bound, every coefficient of the quadratic
profile residual vanishes. -/
theorem coeff_binaryStaircaseProfileResidual_eq_zero_of_two_mul_lt
    (D r M k : ℕ)
    (h : Polynomial K)
    (hdeg : h.natDegree ≤ M)
    (hk : M + M < k) :
    (binaryStaircaseProfileResidual D r h).coeff k = 0 := by
  have hE : (eulerDerivative h).natDegree ≤ M :=
    le_trans (natDegree_eulerDerivative_le h) hdeg
  have hF : (binaryStaircaseProfileSecondEuler h).natDegree ≤ M :=
    le_trans (natDegree_binaryStaircaseProfileSecondEuler_le h) hdeg
  have hhFdeg : (h * binaryStaircaseProfileSecondEuler h).natDegree ≤ M + M :=
    le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hdeg hF)
  have hEEdeg : (eulerDerivative h * eulerDerivative h).natDegree ≤ M + M :=
    le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hE hE)
  have hEFdeg :
      (eulerDerivative h * binaryStaircaseProfileSecondEuler h).natDegree ≤ M + M :=
    le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hE hF)
  have hhFzero :
      (h * binaryStaircaseProfileSecondEuler h).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hhFdeg hk)
  have hEEzero :
      (eulerDerivative h * eulerDerivative h).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hEEdeg hk)
  have hEFzero :
      (eulerDerivative h * binaryStaircaseProfileSecondEuler h).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hEFdeg hk)
  unfold binaryStaircaseProfileResidual
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  rw [hhFzero, hEEzero, hEFzero]
  ring

/-! ## Pure leading monomial -/

/-- Euler derivative of a pure monomial written as `C a * X^N`. -/
theorem eulerDerivative_C_mul_X_pow_profile
    (a : K) (N : ℕ) :
    eulerDerivative (Polynomial.C a * Polynomial.X ^ N) =
      Polynomial.C ((N : K) * a) * Polynomial.X ^ N := by
  ext k
  rw [coeff_eulerDerivative]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  by_cases hk : k = N
  · subst k
    simp [Polynomial.coeff_X_pow]
  · simp [Polynomial.coeff_X_pow, hk, Ne.symm hk]

/-- Falling second Euler derivative of a pure monomial. -/
theorem binaryStaircaseProfileSecondEuler_C_mul_X_pow
    (a : K) (N : ℕ) :
    binaryStaircaseProfileSecondEuler
        (Polynomial.C a * Polynomial.X ^ N) =
      Polynomial.C ((N : K) * ((N : K) - 1) * a) *
        Polynomial.X ^ N := by
  ext k
  rw [coeff_binaryStaircaseProfileSecondEuler]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  by_cases hk : k = N
  · subst k
    simp [Polynomial.coeff_X_pow]
  · simp [Polynomial.coeff_X_pow, hk, Ne.symm hk]

/-- The residual of a pure degree-`N` monomial is divisible by `X^(N+N)`.
For the later next-highest coefficient extraction only this support statement
is needed; the exact coefficient at `2N` is already supplied by
`coeff_add_self_binaryStaircaseProfileResidual`. -/
theorem exists_binaryStaircaseProfileResidual_C_mul_X_pow_factor
    (D r N : ℕ) (a : K) :
    ∃ A : Polynomial K,
      binaryStaircaseProfileResidual D r
          (Polynomial.C a * Polynomial.X ^ N) =
        Polynomial.X ^ (N + N) * A := by
  let e : K := (N : K) * a
  let f : K := (N : K) * ((N : K) - 1) * a
  refine ⟨
    Polynomial.C ((D : K) * ((D : K) - 1)) *
        (Polynomial.C a * Polynomial.C f) -
      Polynomial.C (((D : K) - (r : K)) ^ 2) *
        (Polynomial.C e * Polynomial.C e) -
      Polynomial.C ((r : K) * ((r : K) - 1)) *
        (Polynomial.C e * Polynomial.C f), ?_⟩
  unfold binaryStaircaseProfileResidual
  rw [eulerDerivative_C_mul_X_pow_profile,
    binaryStaircaseProfileSecondEuler_C_mul_X_pow]
  dsimp [e, f]
  rw [pow_add]
  ring

/-! ## Removing the leading monomial -/

/-- Removing the degree-`N` leading monomial really drops degree below `N`.
The proof is coefficientwise, avoiding any dependence on convenience lemmas
for `eraseLead` that are absent from the pinned Mathlib snapshot. -/
theorem natDegree_sub_leadingMonomial_le_pred
    (h : Polynomial K)
    (N : ℕ)
    (hN : N = h.natDegree)
    (hpos : 0 < N) :
    (h - Polynomial.C h.leadingCoeff * Polynomial.X ^ N).natDegree ≤ N - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hkN : N ≤ k := by omega
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  by_cases hEq : k = N
  · subst k
    rw [hN]
    rw [Polynomial.coeff_natDegree]
    simp [Polynomial.coeff_X_pow]
  · have hgt : h.natDegree < k := by
      rw [← hN]
      omega
    have hhzero : h.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hgt
    rw [hhzero]
    simp [Polynomial.coeff_X_pow, hEq, Ne.symm hEq]

/-- A nonzero constant term survives removal of a positive-degree leading
monomial. -/
theorem sub_leadingMonomial_ne_zero_of_coeff_zero_ne_zero
    (h : Polynomial K)
    (N : ℕ)
    (hpos : 0 < N)
    (h0 : h.coeff 0 ≠ 0) :
    h - Polynomial.C h.leadingCoeff * Polynomial.X ^ N ≠ 0 := by
  intro hzero
  have hEq : h = Polynomial.C h.leadingCoeff * Polynomial.X ^ N := by
    exact sub_eq_zero.mp hzero
  have hc := congrArg (fun p : Polynomial K => p.coeff 0) hEq
  have h0N : 0 ≠ N := by omega
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h0N] at hc
  exact h0 hc

/-! ## Complete finite-profile rigidity -/

/-- **Polynomial stationary staircase profile rigidity.**

A finite one-variable profile with nonzero constant term, transverse weight
`r >= 2`, support `deg(h) * r ≤ D`, and zero stationary profile residual has
ordinary degree at most one.

This packages the highest and next-highest coefficient extraction internally
and feeds the two resulting scalar equations into
`binaryFiniteStaircaseProfile_terminal_impossible`. -/
theorem binaryStaircaseProfile_natDegree_le_one
    (D r : ℕ)
    (hr : 2 ≤ r)
    (h : Polynomial K)
    (h0 : h.coeff 0 ≠ 0)
    (hsupport : h.natDegree * r ≤ D)
    (hres : binaryStaircaseProfileResidual D r h = 0) :
    h.natDegree ≤ 1 := by
  by_contra hnot
  let N : ℕ := h.natDegree
  have hN : 2 ≤ N := by
    dsimp [N]
    omega
  have hNpos : 0 < N := by omega
  have hh : h ≠ 0 := by
    intro hz
    rw [hz] at h0
    simp at h0
  let aN : K := h.leadingCoeff
  have haN : aN ≠ 0 := by
    dsimp [aN]
    exact Polynomial.leadingCoeff_ne_zero.mpr hh
  let top : Polynomial K := Polynomial.C aN * Polynomial.X ^ N
  let q : Polynomial K := h - top
  have hqne : q ≠ 0 := by
    dsimp [q, top, aN]
    exact sub_leadingMonomial_ne_zero_of_coeff_zero_ne_zero h N hNpos h0
  have hqdeg : q.natDegree ≤ N - 1 := by
    dsimp [q, top, aN]
    exact natDegree_sub_leadingMonomial_le_pred h N rfl hNpos
  let M : ℕ := q.natDegree
  have hMN : M < N := by
    dsimp [M]
    omega
  let aM : K := q.leadingCoeff
  have haM : aM ≠ 0 := by
    dsimp [aM]
    exact Polynomial.leadingCoeff_ne_zero.mpr hqne
  have htopdeg : top.natDegree ≤ N := by
    dsimp [top]
    calc
      (Polynomial.C aN * Polynomial.X ^ N).natDegree ≤
          (Polynomial.X ^ N).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = N := by simp
  have htopcoeff : top.coeff N = aN := by
    dsimp [top]
    rw [Polynomial.coeff_C_mul]
    simp [Polynomial.coeff_X_pow]
  have hqcoeff : q.coeff M = aM := by
    dsimp [M, aM]
  have hhcoeff : h.coeff N = aN := by
    dsimp [N, aN]

  have hleadingEq :
      aN ^ 2 * binaryStaircaseProfileLeadingScalar (K := K) D r N = 0 := by
    have hc :
        (binaryStaircaseProfileResidual D r h).coeff (N + N) = 0 := by
      rw [hres]
      rfl
    rw [coeff_add_self_binaryStaircaseProfileResidual D r N h
      (by simp [N])] at hc
    rw [hhcoeff] at hc
    exact hc

  have hdecomp : h = top + q := by
    dsimp [q]
    ring
  have hresDecomp :
      binaryStaircaseProfileResidual D r h =
        binaryStaircaseProfileResidual D r top +
          binaryStaircaseProfileCross D r top q +
            binaryStaircaseProfileResidual D r q := by
    rw [hdecomp]
    exact binaryStaircaseProfileResidual_add D r top q
  have htopzero :
      (binaryStaircaseProfileResidual D r top).coeff (N + M) = 0 := by
    dsimp [top]
    obtain ⟨A, hA⟩ :=
      exists_binaryStaircaseProfileResidual_C_mul_X_pow_factor
        (K := K) D r N aN
    rw [hA, Polynomial.coeff_X_pow_mul']
    have hlt : N + M < N + N := by omega
    simp [Nat.not_le.mpr hlt]
  have hqzero :
      (binaryStaircaseProfileResidual D r q).coeff (N + M) = 0 := by
    apply coeff_binaryStaircaseProfileResidual_eq_zero_of_two_mul_lt
      D r M (N + M) q
    · simpa [M]
    · omega
  have hcrosscoeff :
      (binaryStaircaseProfileCross D r top q).coeff (N + M) =
        aN * aM * binaryStaircaseProfileCrossScalar (K := K) D r N M := by
    have hc := coeff_add_binaryStaircaseProfileCross
      (K := K) D r N M top q htopdeg (by simp [M])
    simpa [htopcoeff, hqcoeff] using hc
  have hcrossEq :
      aN * aM * binaryStaircaseProfileCrossScalar (K := K) D r N M = 0 := by
    have hc := congrArg
      (fun p : Polynomial K => p.coeff (N + M)) hresDecomp
    rw [hres] at hc
    simp only [Polynomial.coeff_zero, Polynomial.coeff_add] at hc
    rw [htopzero, hqzero, hcrosscoeff] at hc
    simpa using hc.symm

  have hsupportN : N * r ≤ D := by
    simpa [N] using hsupport
  exact binaryFiniteStaircaseProfile_terminal_impossible
      (K := K)
      (D := D) (r := r) (N := N) (M := M)
      (hr := hr) (hN := hN) (hMN := hMN) (hsupport := hsupportN)
      (aN := aN) (aM := aM) (haN := haN) (haM := haM)
      (hleadingEq := hleadingEq) (hcrossEq := hcrossEq)

/-- Positive-gap HC4 specialization, where `r = delta + 1`. -/
theorem binaryStaircaseProfile_natDegree_le_one_of_positiveGap
    (D delta : ℕ)
    (hdelta : 0 < delta)
    (h : Polynomial K)
    (h0 : h.coeff 0 ≠ 0)
    (hsupport : h.natDegree * (delta + 1) ≤ D)
    (hres : binaryStaircaseProfileResidual D (delta + 1) h = 0) :
    h.natDegree ≤ 1 := by
  exact binaryStaircaseProfile_natDegree_le_one
    (K := K) D (delta + 1) (by omega) h h0 hsupport hres

end

end HC4.Valuation
