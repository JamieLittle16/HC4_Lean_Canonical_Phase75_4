import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity
import Mathlib.Tactic

/-!
# Two-coefficient stationary staircase rigidity

The complete stationary-profile theorem assumes the whole residual polynomial
vanishes, but its proof uses only two coefficients: the highest `N+N`
coefficient and the next-highest `N+M` coefficient after removing the leading
monomial.  R18.21 produces exactly those two coefficients and nothing more.

This module exposes that already-proved finite arithmetic as the minimal
terminal interface.  It reuses the existing leading/cross coefficient formulas
and `binaryFiniteStaircaseProfile_terminal_impossible`; there is no new
recurrence or all-depth argument.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Two exposed residual coefficients already contradict a finite staircase.**

`N` is the actual highest profile degree and `M` the degree left after removing
its leading monomial.  Under the usual support and weight hypotheses, zeros of
only the `N+N` and `N+M` residual coefficients force the same two scalar
equations used by the complete staircase theorem and are therefore impossible. -/
theorem binaryStaircaseProfile_terminal_impossible_of_two_residual_coeffs
    (D r N M : ℕ)
    (hr : 2 ≤ r)
    (h : Polynomial K)
    (h0 : h.coeff 0 ≠ 0)
    (hsupport : h.natDegree * r ≤ D)
    (hN : N = h.natDegree)
    (hNtwo : 2 ≤ N)
    (hM : M =
      (h - Polynomial.C h.leadingCoeff * Polynomial.X ^ N).natDegree)
    (hNN :
      (binaryStaircaseProfileResidual D r h).coeff (N + N) = 0)
    (hNM :
      (binaryStaircaseProfileResidual D r h).coeff (N + M) = 0) :
    False := by
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
    exact natDegree_sub_leadingMonomial_le_pred h N hN hNpos
  have hMq : M = q.natDegree := by
    simpa [q, top, aN] using hM
  have hMN : M < N := by
    rw [hMq]
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
    rw [hMq]
    dsimp [aM]
  have hhcoeff : h.coeff N = aN := by
    rw [hN]
    dsimp [aN]

  have hleadingEq :
      aN ^ 2 * binaryStaircaseProfileLeadingScalar (K := K) D r N = 0 := by
    have hc := hNN
    rw [coeff_add_self_binaryStaircaseProfileResidual D r N h
      (by rw [hN])] at hc
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
    · rw [hMq]
    · omega
  have hcrosscoeff :
      (binaryStaircaseProfileCross D r top q).coeff (N + M) =
        aN * aM * binaryStaircaseProfileCrossScalar (K := K) D r N M := by
    have hc := coeff_add_binaryStaircaseProfileCross
      (K := K) D r N M top q htopdeg (by rw [hMq])
    simpa [htopcoeff, hqcoeff] using hc
  have hcrossEq :
      aN * aM * binaryStaircaseProfileCrossScalar (K := K) D r N M = 0 := by
    have hc := hNM
    rw [hresDecomp] at hc
    simp only [Polynomial.coeff_add] at hc
    rw [htopzero, hqzero, hcrosscoeff] at hc
    simpa using hc

  have hsupportN : N * r ≤ D := by
    rw [hN]
    exact hsupport
  exact binaryFiniteStaircaseProfile_terminal_impossible
      (K := K)
      (D := D) (r := r) (N := N) (M := M)
      (hr := hr) (hN := hNtwo) (hMN := hMN) (hsupport := hsupportN)
      (aN := aN) (aM := aM) (haN := haN) (haM := haM)
      (hleadingEq := hleadingEq) (hcrossEq := hcrossEq)

end

end HC4.Valuation