import HC4.Newton.AdaptivePacketExposure
import HC4.Valuation.PrimitiveSmithEndpoint
import Mathlib.Tactic

/-!
# Integral adaptive diagonal exposure

This is the family-level realization of the combined Smith/ordinary-degree
weight.  Parameter ramification and source weighting are deliberately kept
separate: ramification multiplies pre-existing parameter orders by `R`,
while the source diagonal has the unscaled weight `W_M`.  Consequently the
Hessian clock shift is `R * defect - (4*D-8)`, not its `R`-multiple.

The construction is coefficientwise and therefore never introduces a
Laurent polynomial.  Its sole integrality hypothesis says that the selected
weight `D+2*M` is a lower bound on the source weight of every monomial in the
whole parameter family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Natural-valued form of the combined adaptive source weight. -/
def adaptiveDiagonalRawExponent
    (M : ℕ)
    (d : Fin 4 →₀ ℕ) : ℕ :=
  HC4.Polynomial.ordinaryDegree4 d +
    M * (d 1 + d 2 + 2 * d 3)

theorem adaptiveDiagonalRawExponent_cast
    (M : ℕ)
    (d : Fin 4 →₀ ℕ) :
    (adaptiveDiagonalRawExponent M d : ℤ) =
      Finsupp.weight (adaptivePacketExposureWeight M) d := by
  rw [weight_adaptivePacketExposureWeight]
  unfold adaptiveDiagonalRawExponent
  push_cast
  ring

@[simp] theorem adaptivePacketExposureWeight_longitudinal
    (M : ℕ) :
    adaptivePacketExposureWeight M (0 : Fin 4) = 1 := by
  simp [adaptivePacketExposureWeight]

/-- **Marked-axis obstruction.** Positive ramification cannot make a
section coordinate with nonzero special value divisible by the longitudinal
source factor `X`.  In particular, the combined diagonal exposure cannot
pull back the canonical right marked point, whose longitudinal coordinate
specializes to `1`.

This is why the special-fibre exposure below must not silently be promoted
to a collision-carrying family exposure. -/
theorem not_X_dvd_parameterRamification_of_constantCoeff_ne_zero
    (R : ℕ)
    (hR : 0 < R)
    (a : Polynomial K)
    (ha : Polynomial.constantCoeff a ≠ 0) :
    ¬ Polynomial.X ∣ parameterRamificationHom (K := K) R a := by
  intro hdvd
  have hzero :
      Polynomial.constantCoeff
          (parameterRamificationHom (K := K) R a) = 0 :=
    Polynomial.X_dvd_iff.mp hdvd
  rw [constantCoeff_parameterRamificationHom R hR a] at hzero
  exact ha hzero

/-- Every coefficient is integrally divisible by the scalar source weight
selected by degree `D` on transverse level two. -/
def HasIntegralAdaptiveDiagonalExposure
    (M D : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    D + 2 * M ≤ adaptiveDiagonalRawExponent M d

/-- Coefficient of the honest ramified and normalized diagonal exposure. -/
def adaptiveDiagonalExposureCoefficient
    (R M D : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : Polynomial K :=
  Polynomial.X ^ (adaptiveDiagonalRawExponent M d - (D + 2 * M)) *
    parameterRamificationHom (K := K) R (MvPolynomial.coeff d P)

/-- Honest polynomial family obtained by parameter ramification, the
combined source diagonal, and division by the selected scalar weight. -/
noncomputable def adaptiveDiagonalExposureFamily
    (R M D : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (adaptiveDiagonalExposureCoefficient R M D P d)

theorem coeff_adaptiveDiagonalExposureFamily
    (R M D : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (adaptiveDiagonalExposureFamily R M D P) =
      if d ∈ P.support then
        adaptiveDiagonalExposureCoefficient R M D P d
      else 0 := by
  classical
  unfold adaptiveDiagonalExposureFamily
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

/-- Exact special fibre of the adaptive exposure.  It is the combined
weighted initial form of the original special fibre. -/
theorem polynomialFamilySpecialFiber_adaptiveDiagonalExposureFamily
    (R M D : ℕ)
    (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveDiagonalExposure M D P) :
    polynomialFamilySpecialFiber
        (adaptiveDiagonalExposureFamily R M D P) =
      HC4.Polynomial.initialForm
        (adaptivePacketExposureWeight M)
        ((D : ℤ) + 2 * (M : ℤ))
        (polynomialFamilySpecialFiber P) := by
  classical
  apply MvPolynomial.ext
  intro d
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.coeff_map]
  rw [coeff_adaptiveDiagonalExposureFamily]
  rw [HC4.Polynomial.coeff_initialForm]
  rw [MvPolynomial.coeff_map]
  rw [← adaptiveDiagonalRawExponent_cast]
  by_cases hdP : d ∈ P.support
  · rw [if_pos hdP]
    unfold adaptiveDiagonalExposureCoefficient
    rw [map_mul]
    rw [constantCoeff_parameterRamificationHom R hR]
    have hle : D + 2 * M ≤ adaptiveDiagonalRawExponent M d :=
      hint d hdP
    by_cases heq : adaptiveDiagonalRawExponent M d = D + 2 * M
    · simp [heq]
    · have hpos : 0 < adaptiveDiagonalRawExponent M d - (D + 2 * M) := by
        omega
      have hne : adaptiveDiagonalRawExponent M d - (D + 2 * M) ≠ 0 :=
        Nat.ne_of_gt hpos
      have hweight :
          (adaptiveDiagonalRawExponent M d : ℤ) ≠
            (D : ℤ) + 2 * (M : ℤ) := by
        exact_mod_cast heq
      have hne' : 0 ≠ adaptiveDiagonalRawExponent M d - (D + 2 * M) :=
        Ne.symm hne
      simp [hne', hweight]
  · rw [if_neg hdP]
    have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hdP
    simp [hcoeff]

end

end HC4.Valuation
