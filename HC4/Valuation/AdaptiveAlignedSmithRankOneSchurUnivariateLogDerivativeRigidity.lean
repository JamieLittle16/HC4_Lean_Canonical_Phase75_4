import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLogGradientReduction
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# Stage 4B20: univariate logarithmic-derivative rigidity

Stage 4B19 reduced the rank-one transverse Hessian residual to logarithmic-gradient
identities.  The remaining proportionality step will be obtained by restricting those
identities to affine lines.  This file isolates the one-variable algebra needed for
that restriction.

For nonzero one-variable polynomials over a characteristic-zero field, the identity

    p * q' = q * p'

forces `q` to be a scalar multiple of `p`.

The proof is deliberately fraction-free.  First, if both polynomials have positive
natural degree, comparison of leading coefficients forces their degrees to agree.
Then subtract the unique scalar multiple of `p` that cancels the leading coefficient
of `q`.  The remainder has strictly smaller degree but still satisfies the same
logarithmic-derivative identity.  A nonzero positive-degree remainder would again
have to have the same degree as `p`, contradiction; a nonzero constant remainder
would force `p' = 0`, also a contradiction.
-/

namespace HC4.Valuation

open Polynomial

section

universe u

variable {K : Type u} [Field K] [CharZero K]


/-- Leading coefficient of the derivative in the pinned Mathlib snapshot.  The
upstream convenience theorem is not yet available at this commit, so we derive
it from `degree_derivative_eq` and `coeff_derivative`. -/
private theorem polynomial_leadingCoeff_derivative_of_pos
    (p : Polynomial K)
    (hp : 0 < p.natDegree) :
    p.derivative.leadingCoeff = p.leadingCoeff * (p.natDegree : K) := by
  have hdeg : p.derivative.natDegree = p.natDegree - 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative_eq p hp)
  have hnat : p.natDegree - 1 + 1 = p.natDegree := by omega
  have hcast : ((p.natDegree - 1 : ℕ) : K) + 1 = (p.natDegree : K) := by
    exact_mod_cast hnat
  change p.derivative.coeff p.derivative.natDegree =
    p.leadingCoeff * (p.natDegree : K)
  rw [hdeg, Polynomial.coeff_derivative, hnat, Polynomial.coeff_natDegree, hcast]

/-- If two nonzero positive-degree univariate polynomials have identical logarithmic
formal derivatives, then their natural degrees agree.

This is the leading-coefficient calculation used by the cancellation proof below. -/
theorem polynomial_natDegree_eq_of_logDerivative_cross
    (p q : Polynomial K)
    (hp : p ≠ 0)
    (hq : q ≠ 0)
    (hppos : 0 < p.natDegree)
    (hqpos : 0 < q.natDegree)
    (hcross : p * q.derivative = q * p.derivative) :
    p.natDegree = q.natDegree := by
  have hpLC : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqLC : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hlc0 := congrArg Polynomial.leadingCoeff hcross
  simp only [Polynomial.leadingCoeff_mul] at hlc0
  rw [polynomial_leadingCoeff_derivative_of_pos q hqpos,
    polynomial_leadingCoeff_derivative_of_pos p hppos] at hlc0
  have hlc :
      p.leadingCoeff * (q.leadingCoeff * (q.natDegree : K)) =
        q.leadingCoeff * (p.leadingCoeff * (p.natDegree : K)) := hlc0
  have hcancel :
      (q.natDegree : K) = (p.natDegree : K) := by
    have hcommon :
        (p.leadingCoeff * q.leadingCoeff) * (q.natDegree : K) =
          (p.leadingCoeff * q.leadingCoeff) * (p.natDegree : K) := by
      calc
        (p.leadingCoeff * q.leadingCoeff) * (q.natDegree : K) =
            p.leadingCoeff * (q.leadingCoeff * (q.natDegree : K)) := by ring
        _ = q.leadingCoeff * (p.leadingCoeff * (p.natDegree : K)) := hlc
        _ = (p.leadingCoeff * q.leadingCoeff) * (p.natDegree : K) := by ring
    exact mul_left_cancel₀ (mul_ne_zero hpLC hqLC) hcommon
  exact_mod_cast hcancel.symm

/-- **Univariate logarithmic-derivative rigidity.**

Over a characteristic-zero field, if `p ≠ 0` and

    p * q' = q * p',

then `q` is a constant scalar multiple of `p`.

No gcd, fraction field, or rational-function machinery is used. -/
theorem polynomial_eq_C_mul_of_logDerivative_cross
    (p q : Polynomial K)
    (hp : p ≠ 0)
    (hcross : p * q.derivative = q * p.derivative) :
    ∃ c : K, q = Polynomial.C c * p := by
  by_cases hq : q = 0
  · refine ⟨0, ?_⟩
    simp [hq]
  by_cases hqdeg : q.natDegree = 0
  · have hqder : q.derivative = 0 := Polynomial.derivative_of_natDegree_zero hqdeg
    have hpder : p.derivative = 0 := by
      have hprod : q * p.derivative = 0 := by
        simpa [hqder] using hcross.symm
      exact (mul_eq_zero.mp hprod).resolve_left hq
    have hpdeg : p.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hpder
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hpdeg
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have hp0 : p.coeff 0 ≠ 0 := by
      intro h0
      apply hp
      rw [hpC, h0]
      simp
    refine ⟨q.coeff 0 / p.coeff 0, ?_⟩
    have hscalar : q.coeff 0 / p.coeff 0 * p.coeff 0 = q.coeff 0 :=
      div_mul_cancel₀ _ hp0
    calc
      q = Polynomial.C (q.coeff 0) := hqC
      _ = Polynomial.C ((q.coeff 0 / p.coeff 0) * p.coeff 0) :=
        congrArg Polynomial.C hscalar.symm
      _ = Polynomial.C (q.coeff 0 / p.coeff 0) * Polynomial.C (p.coeff 0) := by
        rw [Polynomial.C_mul]
      _ = Polynomial.C (q.coeff 0 / p.coeff 0) * p := by rw [← hpC]
  have hqpos : 0 < q.natDegree := Nat.pos_of_ne_zero hqdeg
  have hppos : 0 < p.natDegree := by
    by_contra hpnot
    have hpdeg : p.natDegree = 0 := Nat.eq_zero_of_not_pos hpnot
    have hpder : p.derivative = 0 := Polynomial.derivative_of_natDegree_zero hpdeg
    have hprod : p * q.derivative = 0 := by
      simpa [hpder] using hcross
    have hqder : q.derivative = 0 := (mul_eq_zero.mp hprod).resolve_left hp
    exact hqdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hqder)
  have hdegNat : p.natDegree = q.natDegree :=
    polynomial_natDegree_eq_of_logDerivative_cross p q hp hq hppos hqpos hcross
  let c : K := q.leadingCoeff / p.leadingCoeff
  let s : Polynomial K := Polynomial.C c * p
  let r : Polynomial K := q - s
  have hpLC : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqLC : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero hqLC hpLC
  have hcu : IsUnit c := isUnit_iff_ne_zero.mpr hc
  have hsdeg : s.degree = p.degree := by
    dsimp [s]
    exact Polynomial.degree_C_mul_of_isUnit hcu p
  have hslc : s.leadingCoeff = q.leadingCoeff := by
    dsimp [s]
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit hcu]
    dsimp [c]
    field_simp
  have hqdegp : q.degree = p.degree := by
    rw [Polynomial.degree_eq_natDegree hq, Polynomial.degree_eq_natDegree hp]
    exact_mod_cast hdegNat.symm
  have hqdegs : q.degree = s.degree := hqdegp.trans hsdeg.symm
  have hrdeg : r.degree < q.degree := by
    dsimp [r]
    exact Polynomial.degree_sub_lt hqdegs hq hslc.symm
  have hcrossr : p * r.derivative = r * p.derivative := by
    dsimp [r, s]
    rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul]
    calc
      p * (q.derivative - Polynomial.C c * p.derivative) =
          p * q.derivative - Polynomial.C c * (p * p.derivative) := by ring
      _ = q * p.derivative - Polynomial.C c * (p * p.derivative) := by rw [hcross]
      _ = (q - Polynomial.C c * p) * p.derivative := by ring
  have hrzero : r = 0 := by
    by_contra hr
    by_cases hrdeg0 : r.natDegree = 0
    · have hrder : r.derivative = 0 := Polynomial.derivative_of_natDegree_zero hrdeg0
      have hprod : r * p.derivative = 0 := by
        simpa [hrder] using hcrossr.symm
      have hpder : p.derivative = 0 := (mul_eq_zero.mp hprod).resolve_left hr
      exact (Nat.ne_of_gt hppos) (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hpder)
    · have hrpos : 0 < r.natDegree := Nat.pos_of_ne_zero hrdeg0
      have heq : p.natDegree = r.natDegree :=
        polynomial_natDegree_eq_of_logDerivative_cross p r hp hr hppos hrpos hcrossr
      have hrltq : r.natDegree < q.natDegree :=
        Polynomial.natDegree_lt_natDegree hr hrdeg
      omega
  refine ⟨c, ?_⟩
  have : q = s := sub_eq_zero.mp (by simpa [r] using hrzero)
  simpa [s] using this

end

end HC4.Valuation
