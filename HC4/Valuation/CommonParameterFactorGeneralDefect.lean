import HC4.Valuation.CommonParameterFactorRestart
import Mathlib.Tactic

/-!
# A18.5.14: arbitrary common parameter factors and the Hessian clock

`CommonParameterFactorRestart` proves the four-dimensional defect calculation
for one common factor `X`.  Terminal normalization needs the same statement
for the exact attained minimum coefficient order `m` in one step.

If

    P = X^m Q
    det Hess(P) = X^Delta,

then scalar multiplication of a four-variable potential contributes four
copies of the scalar to the Hessian determinant.  Hence

    4*m <= Delta
    det Hess(Q) = X^(Delta - 4*m).

Everything stays in the polynomial ring; no valuation quotient or rational
scale is introduced.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Removing a common `X^m` from a four-variable potential forces at least
`4*m` powers in its pure Hessian clock. -/
theorem four_mul_le_defect_of_commonParameterFactor
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor m P)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    4 * m ≤ Delta := by
  let Q := commonParameterFactorFamily m P hdiv
  have hfactor :
      P = MvPolynomial.C (Polynomial.X ^ m) * Q :=
    commonParameterFactorFamily_factorisation m P hdiv
  have hdet := congrArg HC4.Polynomial.hessianDeterminant hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef] at hdet
  have hdvdMv :
      (MvPolynomial.C (Polynomial.X ^ (4 * m)) :
          MvPolynomial (Fin 4) (Polynomial K)) ∣
        MvPolynomial.C (Polynomial.X ^ Delta) := by
    refine ⟨HC4.Polynomial.hessianDeterminant Q, ?_⟩
    have hpow : (Polynomial.X ^ m : Polynomial K) ^ 4 =
        Polynomial.X ^ (4 * m) := by
      rw [← pow_mul]
      congr 1
      omega
    simpa [MvPolynomial.C_pow, hpow, Q] using hdet
  have hdvdPoly :
      (Polynomial.X ^ (4 * m) : Polynomial K) ∣
        Polynomial.X ^ Delta := by
    have hall :=
      (MvPolynomial.C_dvd_iff_dvd_coeff
        (Polynomial.X ^ (4 * m))
        (MvPolynomial.C (Polynomial.X ^ Delta) :
          MvPolynomial (Fin 4) (Polynomial K))).mp hdvdMv
    simpa only [MvPolynomial.coeff_zero_C] using
      (hall (0 : Fin 4 →₀ ℕ))
  rcases hdvdPoly with ⟨R, hR⟩
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hR
    exact (pow_ne_zero Delta Polynomial.X_ne_zero) hR
  have hXm :
      (Polynomial.X ^ (4 * m) : Polynomial K) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hdeg : Delta = 4 * m + R.natDegree := by
    calc
      Delta = (Polynomial.X ^ Delta : Polynomial K).natDegree := by simp
      _ = ((Polynomial.X ^ (4 * m) : Polynomial K) * R).natDegree := by
        rw [hR]
      _ = (Polynomial.X ^ (4 * m) : Polynomial K).natDegree + R.natDegree := by
        exact Polynomial.natDegree_mul hXm hRne
      _ = 4 * m + R.natDegree := by simp
  omega

/-- **Exact arbitrary common-factor defect formula.** -/
theorem commonParameterFactor_hasHessianDefect_sub_four_mul
    (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor m P)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (commonParameterFactorFamily m P hdiv)
      (Delta - 4 * m) := by
  let Q := commonParameterFactorFamily m P hdiv
  have hle : 4 * m ≤ Delta :=
    four_mul_le_defect_of_commonParameterFactor m P hdiv Delta hdef
  have hfactor :
      P = MvPolynomial.C (Polynomial.X ^ m) * Q :=
    commonParameterFactorFamily_factorisation m P hdiv
  have hdet := congrArg HC4.Polynomial.hessianDeterminant hfactor
  rw [hessianDeterminant_C_mul] at hdet
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hdef] at hdet
  have hpowPoly :
      (Polynomial.X ^ m : Polynomial K) ^ 4 *
          Polynomial.X ^ (Delta - 4 * m) =
        Polynomial.X ^ Delta := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hpowMv :
      (MvPolynomial.C (Polynomial.X ^ m) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C (Polynomial.X ^ (Delta - 4 * m)) =
      MvPolynomial.C (Polynomial.X ^ Delta) := by
    rw [← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
    exact congrArg MvPolynomial.C hpowPoly
  have hcancel :
      (MvPolynomial.C (Polynomial.X ^ m) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        MvPolynomial.C (Polynomial.X ^ (Delta - 4 * m)) =
      (MvPolynomial.C (Polynomial.X ^ m) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        HC4.Polynomial.hessianDeterminant Q := by
    calc
      _ = MvPolynomial.C (Polynomial.X ^ Delta) := hpowMv
      _ = _ := by simpa [Q] using hdet
  have hfac :
      (MvPolynomial.C (Polynomial.X ^ m) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 ≠ 0 := by
    exact pow_ne_zero 4
      (MvPolynomial.C_ne_zero.mpr (pow_ne_zero m Polynomial.X_ne_zero))
  have hz :
      (MvPolynomial.C (Polynomial.X ^ m) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        (MvPolynomial.C (Polynomial.X ^ (Delta - 4 * m)) -
          HC4.Polynomial.hessianDeterminant Q) = 0 := by
    rw [mul_sub, hcancel, sub_self]
  have hsub :
      MvPolynomial.C (Polynomial.X ^ (Delta - 4 * m)) -
        HC4.Polynomial.hessianDeterminant Q = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfac hzero)
    · exact hzero
  exact (sub_eq_zero.mp hsub).symm

end

end HC4.Valuation
