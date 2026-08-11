import HC4.Valuation.StrictSmithMaximalNormalization
import HC4.Valuation.PrimitiveSmithEndpoint
import Mathlib.Tactic

/-!
# Exact geometry of the strict-Smith first-contact transform

This file records the exact coefficient order created by the fixed strict
symmetric Smith transform before maximal common-parameter normalisation.

For a supported source coefficient of exact parameter order `v`, the strict
Smith construction first ramifies the parameter by `10`, then performs the
integral `(2,2)` Smith transform and divides by its conformal multiplier
`X^4`.  The resulting coefficient has exact order

    raw(d) + 10 * v - 4.

The statement is deliberately independent of any proposed global progress
measure.  It is the coefficientwise input needed to analyse the maximally
normalised first-contact face honestly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Generic positive ramification facts -/

/-- A supported source monomial remains supported after any positive
parameter ramification. -/
theorem mem_parameterRamificationFamily_support_of_mem_pos
    (R : ℕ)
    (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    d ∈ (parameterRamificationFamily (K := K) R P).support := by
  apply MvPolynomial.mem_support_iff.mpr
  unfold parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  apply parameterRamificationHom_ne_zero_of_pos R hR
  exact MvPolynomial.mem_support_iff.mp hd

/-- Exact ramified factorisation of a supported source coefficient for an
arbitrary ramification index. -/
theorem parameterRamification_sourceCoefficient_factorisation
    (R : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (parameterRamificationFamily (K := K) R P) =
      Polynomial.X ^ (R * smithFamilyCoefficientOrder P d) *
        parameterRamificationHom (K := K) R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
  have hcoeff : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have horder :
      smithFamilyCoefficientOrder P d =
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff := by
    rw [smithFamilyCoefficientOrder_eq P hd]
    rfl
  have hprimitive :=
    polynomialParameterPrimitivePart_spec
      (MvPolynomial.coeff d P) hcoeff
  unfold parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  calc
    parameterRamificationHom (K := K) R (MvPolynomial.coeff d P) =
        parameterRamificationHom (K := K) R
          (Polynomial.X ^
              (polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff) *
            polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P) hcoeff) :=
      congrArg (parameterRamificationHom (K := K) R) hprimitive
    _ = Polynomial.X ^
          (R * polynomialParameterOrder (MvPolynomial.coeff d P) hcoeff) *
        parameterRamificationHom (K := K) R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P) hcoeff) := by
      rw [map_mul, parameterRamificationHom_X_pow]
    _ = Polynomial.X ^ (R * smithFamilyCoefficientOrder P d) *
        parameterRamificationHom (K := K) R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P) hcoeff) := by
      rw [horder]

/-- If a nonzero polynomial is written as an exact `X^n` power times a
primitive factor, then its selected parameter order is exactly `n`. -/
theorem polynomialParameterOrder_eq_of_exact_X_power_factorisation
    (c : Polynomial K)
    (hc : c ≠ 0)
    (n : ℕ)
    (u : Polynomial K)
    (hu : Polynomial.constantCoeff u ≠ 0)
    (hfactor : c = Polynomial.X ^ n * u) :
    polynomialParameterOrder c hc = n := by
  have hdiv : Polynomial.X ^ n ∣ c := ⟨u, hfactor⟩
  have hle : n ≤ polynomialParameterOrder c hc :=
    polynomial_X_pow_dvd_le_parameterOrder c hc n hdiv
  let a := polynomialParameterOrder c hc
  let primitive := polynomialParameterPrimitivePart c hc
  have hprimitive : c = Polynomial.X ^ a * primitive := by
    simpa [a, primitive] using polynomialParameterPrimitivePart_spec c hc
  have hprimitiveConst : Polynomial.constantCoeff primitive ≠ 0 := by
    simpa [primitive] using
      polynomialParameterPrimitivePart_constantCoeff_ne_zero c hc
  have heq : Polynomial.X ^ n * u = Polynomial.X ^ a * primitive :=
    hfactor.symm.trans hprimitive
  have hna : n = a :=
    (maximalCommonParameter_constantCoeff_ne_zero_iff
      (a := a) (m := n) (u := primitive) (v := u)
      (by simpa [a] using hle) hprimitiveConst heq).mp hu
  simpa [a] using hna.symm

/-! ## The exact strict-Smith transformed order -/

/-- The actual integral Smith family used by the strict symmetric
improvement branch, before common-parameter extraction. -/
noncomputable def strictSymmetricSmithTransformedFamily
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ))) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  integralSmithConformalFamily
    2 2
    (parameterRamificationFamily (K := K) 10 P)
    (strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base P hbase hstrict)

/-- Exact residual parameter exponent of a source monomial after the fixed
ramification-by-ten strict Smith transform and the conformal `X^4`
normalisation. -/
def strictSmithResidualExponent
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ :=
  smithConformalRawExponent 2 2 d +
      10 * smithFamilyCoefficientOrder P d - 4

/-- On every source monomial of the original family, strict symmetric Smith
improvement gives an exact coefficient factorisation.  In particular, the
residual exponent is not merely a divisibility lower bound. -/
theorem strictSymmetricImprovement_coefficient_exactFactorisation
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (strictSymmetricSmithTransformedFamily base P hbase hstrict) =
      Polynomial.X ^ (strictSmithResidualExponent P d) *
        parameterRamificationHom (K := K) 10
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
  let Pram := parameterRamificationFamily (K := K) 10 P
  let hsmith :=
    strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base P hbase hstrict
  have hdRam : d ∈ Pram.support := by
    dsimp [Pram]
    exact mem_parameterRamificationFamily_support_of_mem_pos
      (K := K) 10 (by omega) P hd
  have hcoeff :
      MvPolynomial.coeff d
          (strictSymmetricSmithTransformedFamily base P hbase hstrict) =
        smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
    unfold strictSymmetricSmithTransformedFamily
    exact coeff_integralSmithConformalFamily_of_mem
      2 2 Pram hsmith hdRam
  rw [hcoeff]
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      2 2 Pram hsmith hdRam
  have hfactor :=
    parameterRamification_sourceCoefficient_factorisation
      (K := K) 10 P hd
  have hfactor' :
      MvPolynomial.coeff d Pram =
        Polynomial.X ^ (10 * smithFamilyCoefficientOrder P d) *
          parameterRamificationHom (K := K) 10
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [Pram] using hfactor
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hbaselePoly :
      base (smithAxisProjection d) ≤
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne :=
    polynomial_X_pow_dvd_le_parameterOrder
      (MvPolynomial.coeff d P) hcoeffne
      (base (smithAxisProjection d))
      (hbase d hd)
  have horder :
      smithFamilyCoefficientOrder P d =
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
    rw [smithFamilyCoefficientOrder_eq P hd]
    rfl
  have hbasele :
      base (smithAxisProjection d) ≤ smithFamilyCoefficientOrder P d := by
    omega
  have hfive :
      5 ≤ smithConformalRawExponent 2 2 d +
        10 * base (smithAxisProjection d) :=
    strictSymmetricImprovement_raw_plus_base_ge_five
      (K := K) base P hstrict hd
  have hle0 :
      4 ≤ smithConformalRawExponent 2 2 d +
        10 * smithFamilyCoefficientOrder P d := by
    omega
  let r := strictSmithResidualExponent P d
  have hr0 :
      4 + strictSmithResidualExponent P d =
        smithConformalRawExponent 2 2 d +
          10 * smithFamilyCoefficientOrder P d := by
    unfold strictSmithResidualExponent
    exact Nat.add_sub_of_le hle0
  have hr :
      4 + r =
        smithConformalRawExponent 2 2 d +
          10 * smithFamilyCoefficientOrder P d := by
    simpa [r] using hr0
  have heq :
      Polynomial.X ^ 4 *
          (Polynomial.X ^ r *
            parameterRamificationHom (K := K) 10
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d P)
                (MvPolynomial.mem_support_iff.mp hd))) =
        Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
    calc
      Polynomial.X ^ 4 *
          (Polynomial.X ^ r *
            parameterRamificationHom (K := K) 10
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d P)
                (MvPolynomial.mem_support_iff.mp hd))) =
        Polynomial.X ^ (4 + r) *
          parameterRamificationHom (K := K) 10
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
          rw [pow_add]
          ring
      _ = Polynomial.X ^
            (smithConformalRawExponent 2 2 d +
              10 * smithFamilyCoefficientOrder P d) *
          parameterRamificationHom (K := K) 10
            (polynomialParameterPrimitivePart
              (MvPolynomial.coeff d P)
              (MvPolynomial.mem_support_iff.mp hd)) := by
          rw [hr]
      _ = Polynomial.X ^ (smithConformalRawExponent 2 2 d) *
          (Polynomial.X ^ (10 * smithFamilyCoefficientOrder P d) *
            parameterRamificationHom (K := K) 10
              (polynomialParameterPrimitivePart
                (MvPolynomial.coeff d P)
                (MvPolynomial.mem_support_iff.mp hd))) := by
          rw [pow_add]
          ring
      _ = smithConformalCoefficientFactor (K := K) 2 2 d *
          MvPolynomial.coeff d Pram := by
          rw [smithConformalCoefficientFactor_two_two, hfactor']
      _ = smithConformalMultiplier (K := K) 2 2 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := hspec
      _ = Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient 2 2 Pram hsmith d := by
          simp [smithConformalMultiplier,
            smithConformalMultiplierExponent]
  have hcancel := polynomial_X_pow_mul_cancel (K := K) 4 heq
  simpa [r] using hcancel.symm

/-- Strictness leaves at least one exact parameter power after conformal
normalisation on every original source monomial. -/
theorem strictSymmetricImprovement_residualExponent_pos
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    0 < strictSmithResidualExponent P d := by
  have hcoeffne : MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hbaselePoly :
      base (smithAxisProjection d) ≤
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne :=
    polynomial_X_pow_dvd_le_parameterOrder
      (MvPolynomial.coeff d P) hcoeffne
      (base (smithAxisProjection d))
      (hbase d hd)
  have horder :
      smithFamilyCoefficientOrder P d =
        polynomialParameterOrder (MvPolynomial.coeff d P) hcoeffne := by
    rw [smithFamilyCoefficientOrder_eq P hd]
    rfl
  have hbasele :
      base (smithAxisProjection d) ≤ smithFamilyCoefficientOrder P d := by
    omega
  have hfive :
      5 ≤ smithConformalRawExponent 2 2 d +
        10 * base (smithAxisProjection d) :=
    strictSymmetricImprovement_raw_plus_base_ge_five
      (K := K) base P hstrict hd
  unfold strictSmithResidualExponent
  omega

/-- The exact parameter order of every transformed source coefficient is its
strict-Smith residual exponent. -/
theorem strictSymmetricImprovement_transformedCoefficientOrder_eq_residual
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    smithFamilyCoefficientOrder
        (strictSymmetricSmithTransformedFamily base P hbase hstrict) d =
      strictSmithResidualExponent P d := by
  let Psmith := strictSymmetricSmithTransformedFamily base P hbase hstrict
  let primitive :=
    polynomialParameterPrimitivePart
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)
  let ramPrimitive := parameterRamificationHom (K := K) 10 primitive
  have hfactor :
      MvPolynomial.coeff d Psmith =
        Polynomial.X ^ (strictSmithResidualExponent P d) * ramPrimitive := by
    simpa [Psmith, primitive, ramPrimitive] using
      strictSymmetricImprovement_coefficient_exactFactorisation
        (K := K) base P hbase hstrict hd
  have hprimitiveConst : Polynomial.constantCoeff primitive ≠ 0 := by
    simpa [primitive] using
      polynomialParameterPrimitivePart_constantCoeff_ne_zero
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd)
  have hramPrimitiveConst : Polynomial.constantCoeff ramPrimitive ≠ 0 := by
    change Polynomial.constantCoeff
        (parameterRamificationHom (K := K) 10 primitive) ≠ 0
    rw [constantCoeff_parameterRamificationHom (K := K) 10 (by omega)]
    exact hprimitiveConst
  have hramPrimitiveNe : ramPrimitive ≠ 0 := by
    intro hzero
    rw [hzero] at hramPrimitiveConst
    simp at hramPrimitiveConst
  have hcoeffne : MvPolynomial.coeff d Psmith ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero
      (pow_ne_zero _ Polynomial.X_ne_zero)
      hramPrimitiveNe
  have hdSmith : d ∈ Psmith.support :=
    MvPolynomial.mem_support_iff.mpr hcoeffne
  have hparameter :
      polynomialParameterOrder
          (MvPolynomial.coeff d Psmith) hcoeffne =
        strictSmithResidualExponent P d :=
    polynomialParameterOrder_eq_of_exact_X_power_factorisation
      (K := K)
      (MvPolynomial.coeff d Psmith) hcoeffne
      (strictSmithResidualExponent P d) ramPrimitive
      hramPrimitiveConst hfactor
  rw [smithFamilyCoefficientOrder_eq Psmith hdSmith]
  simpa [smithFamilyCoefficientParameterOrder] using hparameter

/-- A nonzero input family remains nonzero after the strict Smith transform.
This supplies the nonzeroness hypothesis needed by maximal normalisation. -/
theorem strictSymmetricImprovement_transformedFamily_ne_zero
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    (hP : P ≠ 0) :
    strictSymmetricSmithTransformedFamily base P hbase hstrict ≠ 0 := by
  rcases MvPolynomial.support_nonempty.mpr hP with ⟨d, hd⟩
  let Psmith := strictSymmetricSmithTransformedFamily base P hbase hstrict
  have hfactor :=
    strictSymmetricImprovement_coefficient_exactFactorisation
      (K := K) base P hbase hstrict hd
  let primitive :=
    polynomialParameterPrimitivePart
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)
  let ramPrimitive := parameterRamificationHom (K := K) 10 primitive
  have hramPrimitiveNe : ramPrimitive ≠ 0 := by
    dsimp [ramPrimitive, primitive]
    apply parameterRamificationHom_ne_zero_of_pos 10 (by omega)
    intro hzero
    have hconst :=
      polynomialParameterPrimitivePart_constantCoeff_ne_zero
        (MvPolynomial.coeff d P)
        (MvPolynomial.mem_support_iff.mp hd)
    rw [hzero] at hconst
    simp at hconst
  have hfactor' :
      MvPolynomial.coeff d Psmith =
        Polynomial.X ^ (strictSmithResidualExponent P d) * ramPrimitive := by
    simpa [Psmith, primitive, ramPrimitive] using hfactor
  have hcoeffne :
      MvPolynomial.coeff d Psmith ≠ 0 := by
    rw [hfactor']
    exact mul_ne_zero
      (pow_ne_zero (strictSmithResidualExponent P d) Polynomial.X_ne_zero)
      hramPrimitiveNe
  intro hzero
  apply hcoeffne
  dsimp [Psmith]
  rw [hzero]
  simp

end

end HC4.Valuation
