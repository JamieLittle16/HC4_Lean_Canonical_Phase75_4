import HC4.Newton.SymmetricSmithMinimality
import HC4.Valuation.CommonParameterFactorRestart
import Mathlib.Tactic

/-!
# Strict symmetric Smith improvement gives a fixed-scale global restart

Phase 93.62 shows that the canonical Smith classifier needs only the fixed
separator `(k,l) = (1,1)`.  Its integral direction is `(2,2)` and its
denominator-clearing ramification index is exactly `10`.

This file closes the complementary algebraic branch on that single fixed
scale.

Suppose a primitive polynomial family `P` carries a natural lower-bound
certificate

    tau^(base(e)) | coefficient_d(P)

for every source monomial whose Smith projection is `e`.

If the symmetric separator strictly improves every projected support value,
then after the once-for-all ramification

    tau = s^10

the integral `(2,2)` Smith conformal transform exists.  Moreover, after
normalisation by its conformal multiplier `s^4`, every transformed
coefficient still contains at least one factor of `s`.

Hence the transformed family has a common parameter factor.  Phase 93.61
then removes that factor and drops the fixed-scale Hessian defect by exactly
four:

    10*Delta  ->  10*Delta - 4.

The same fixed ramification also gives enough divisibility of transverse
moving-section coordinates to apply the exact collision covariance theorem
from Phase 93.59.

Thus the complementary Smith branch is now a genuine strict
`GlobalRestartProgress` step on one fixed ramified defect scale.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Elementary parameter-power divisibility -/

/-- Lower parameter powers divide higher parameter powers. -/
theorem polynomial_X_pow_dvd_X_pow_of_le
    (a b : ℕ)
    (h : a ≤ b) :
    (Polynomial.X ^ a : Polynomial K) ∣
      Polynomial.X ^ b := by
  refine
    ⟨Polynomial.X ^ (b - a), ?_⟩
  rw [← pow_add]
  congr 1
  omega

/-- Cancel the common `X^n` from the divisibility
`X^(n+1) | X^n * q`. -/
theorem polynomial_X_dvd_of_succ_pow_dvd_pow_mul
    (n : ℕ)
    (q : Polynomial K)
    (h :
      Polynomial.X ^ (n + 1) ∣
        Polynomial.X ^ n * q) :
    Polynomial.X ∣ q := by
  rcases h with ⟨r, hr⟩
  have heq :
      Polynomial.X ^ n * q =
        Polynomial.X ^ n *
          (Polynomial.X * r) := by
    calc
      Polynomial.X ^ n * q =
          Polynomial.X ^ (n + 1) * r := hr
      _ =
          Polynomial.X ^ n *
            (Polynomial.X * r) := by
              rw [pow_succ]
              ring
  have hfac :
      (Polynomial.X ^ n : Polynomial K) ≠ 0 :=
    pow_ne_zero n Polynomial.X_ne_zero
  have hz :
      Polynomial.X ^ n *
        (q - Polynomial.X * r) = 0 := by
    rw [mul_sub, heq, sub_self]
  have hsub :
      q - Polynomial.X * r = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfac hzero)
    · exact hzero
  refine ⟨r, ?_⟩
  exact sub_eq_zero.mp hsub

/-! ## Smith projection and coefficient-order certificate -/

/-- The canonical Smith projection in the fixed ordered coordinates
`(x,y,z,w) = (0,1,2,3)`. -/
def smithAxisProjection
    (d : Fin 4 →₀ ℕ) :
    SmithSupportExponent :=
  smithSupportExponentOf
    (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) d

/-- Smith projected support for a Rees family over `K[tau]`.

The older `smithProjectedSupport` is field-valued because it was introduced
for the special-fibre polynomial.  Here coefficients lie in `Polynomial K`,
so we use the underlying source support directly; no coefficient-field
assumption is mathematically needed for this finite projection. -/
noncomputable def smithAxisProjectedSupport
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Finset SmithSupportExponent := by
  classical
  exact P.support.image smithAxisProjection

/-- Natural lower bounds on the parameter order of every family
coefficient, indexed by its Smith projection. -/
def HasSmithCoefficientOrderLowerBound
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    Polynomial.X ^ (base (smithAxisProjection d)) ∣
      MvPolynomial.coeff d P

/-- The Smith projection of every source exponent in the source support lies
in the actual projected support. -/
theorem smithAxisProjection_mem_projectedSupport
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    smithAxisProjection d ∈
      smithAxisProjectedSupport (K := K) P := by
  classical
  unfold smithAxisProjectedSupport
  exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-! ## Exact exponent arithmetic for the fixed separator -/

/-- The `(2,2)` Smith coefficient factor is the expected pure parameter
power. -/
theorem smithConformalCoefficientFactor_two_two
    (d : Fin 4 →₀ ℕ) :
    smithConformalCoefficientFactor
        (K := K) 2 2 d =
      Polynomial.X ^
        smithConformalRawExponent 2 2 d := by
  unfold smithConformalCoefficientFactor
  rw [Fin.prod_univ_four]
  simp only [
    smithConformalDerivativeCoefficient,
    smithConformalSourceExponent,
    smithConformalRawExponent]
  simp
  calc
    (Polynomial.X ^ 2) ^ d 1 *
          (Polynomial.X ^ 2) ^ d 2 *
          (Polynomial.X ^ 4) ^ d 3 =
        Polynomial.X ^ (2 * d 1) *
          Polynomial.X ^ (2 * d 2) *
          Polynomial.X ^ (4 * d 3) := by
            simp only [← pow_mul]
    _ =
        Polynomial.X ^
          (2 * d 1 + 2 * d 2 + 4 * d 3) := by
            rw [← pow_add, ← pow_add]
    _ =
        Polynomial.X ^
          smithConformalRawExponent 2 2 d := by
            rfl

/-- The denominator-cleared symmetric Smith value is exactly

    10*base + rawExponent - 4

on a concrete source exponent. -/
theorem smithIntegralSeparatorTilt_one_one_projection
    (base : SmithSupportExponent → ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithIntegralSeparatorTilt
        1 1
        (fun e => (base e : ℤ))
        (smithAxisProjection d) =
      (10 : ℤ) * (base (smithAxisProjection d) : ℤ) +
        (smithConformalRawExponent 2 2 d : ℤ) -
        4 := by
  have hdelta :
      smithSeparatorDelta
          1 1 (smithAxisProjection d) =
        (smithConformalRawExponent 2 2 d : ℤ) - 4 := by
    unfold smithSeparatorDelta
    rw [HC4.Newton.smithExtremeSeparator_one_one]
    have h :=
      smithConformalRawExponent_sub_multiplier_eq_gradeDot
        2 2 d
    simpa [smithAxisProjection,
      SmithSupportExponent.grade,
      smithConformalMultiplierExponent] using h.symm
  unfold smithIntegralSeparatorTilt
  unfold finiteIntegralRescaledTilt
  rw [HC4.Newton.smithExtremeSeparatorBound_one_one]
  norm_num [finiteTiltDenominator]
  rw [hdelta]
  ring

/-- A strict symmetric improvement at old minimum zero gives at least five
raw powers after the fixed ramification and source inflation.  Four are
spent on the conformal multiplier, leaving at least one common factor. -/
theorem strictSymmetricImprovement_raw_plus_base_ge_five
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    5 ≤
      smithConformalRawExponent 2 2 d +
        10 * base (smithAxisProjection d) := by
  have he :=
    smithAxisProjection_mem_projectedSupport (K := K) P hd
  have himprove :=
    hstrict (smithAxisProjection d) he
  have htilt :
      (0 : ℤ) <
        (10 : ℤ) *
            (base (smithAxisProjection d) : ℤ) +
          (smithConformalRawExponent 2 2 d : ℤ) -
          4 := by
    simpa [smithRescaledOldMinimum,
      finiteTiltDenominator,
      smithExtremeSeparatorBound] using
      (show
        smithRescaledOldMinimum 1 1 (0 : ℤ) <
          smithIntegralSeparatorTilt
            1 1
            (fun e => (base e : ℤ))
            (smithAxisProjection d) from himprove)
      |>.trans_eq
        (smithIntegralSeparatorTilt_one_one_projection
          base d)
  have hz :
      (5 : ℤ) ≤
        (smithConformalRawExponent 2 2 d : ℤ) +
          10 * (base (smithAxisProjection d) : ℤ) := by
    omega
  exact_mod_cast hz

/-! ## Fixed ramification transports the base lower bound -/

/-- After `tau = s^10`, every source coefficient has the corresponding
order lower bound multiplied by ten. -/
theorem smithCoefficientOrderLowerBound_after_ramification_ten
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase :
      HasSmithCoefficientOrderLowerBound
        base P) :
    HasParameterCoefficientDivisibility
      (fun d => 10 * base (smithAxisProjection d))
      (parameterRamificationFamily
        (K := K) 10 P) := by
  exact
    parameterRamificationFamily_coefficientDivisibility
      (K := K)
      10
      (fun d => base (smithAxisProjection d))
      P
      hbase

/-! ## Strict improvement makes the Smith transform integral -/

/-- **The fixed `(2,2)` Smith transform is integral under strict symmetric
improvement.** -/
theorem strictSymmetricImprovement_integralSmithDivisibility
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase :
      HasSmithCoefficientOrderLowerBound
        base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ))) :
    HasIntegralSmithConformalCoefficientDivisibility
      2 2
      (parameterRamificationFamily
        (K := K) 10 P) := by
  let Pram :=
    parameterRamificationFamily
      (K := K) 10 P
  have hram :=
    smithCoefficientOrderLowerBound_after_ramification_ten
      (K := K) base P hbase
  intro d hd
  have hdP :
      d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom (K := K) 10)
      P) hd
  have hcoeff :
      Polynomial.X ^
          (10 * base (smithAxisProjection d)) ∣
        MvPolynomial.coeff d Pram := by
    exact hram d hd
  have hfive :
      5 ≤
        smithConformalRawExponent 2 2 d +
          10 * base (smithAxisProjection d) :=
    strictSymmetricImprovement_raw_plus_base_ge_five
      (K := K) base P hstrict hdP
  have hfour :
      4 ≤
        smithConformalRawExponent 2 2 d +
          10 * base (smithAxisProjection d) := by
    omega
  have hfactor :
      smithConformalCoefficientFactor
          (K := K) 2 2 d =
        Polynomial.X ^
          smithConformalRawExponent 2 2 d :=
    smithConformalCoefficientFactor_two_two (K := K) d
  have htotal :
      Polynomial.X ^
          (smithConformalRawExponent 2 2 d +
            10 * base (smithAxisProjection d)) ∣
        smithConformalCoefficientFactor
            (K := K) 2 2 d *
          MvPolynomial.coeff d Pram := by
    rcases hcoeff with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [hfactor, hr]
    calc
      Polynomial.X ^
            smithConformalRawExponent 2 2 d *
          (Polynomial.X ^
              (10 * base (smithAxisProjection d)) *
            r) =
        (Polynomial.X ^
            smithConformalRawExponent 2 2 d *
          Polynomial.X ^
            (10 * base (smithAxisProjection d))) *
          r := by ring
      _ =
        Polynomial.X ^
            (smithConformalRawExponent 2 2 d +
              10 * base (smithAxisProjection d)) *
          r := by
            rw [← pow_add]
  have hsmall :
      (Polynomial.X ^ 4 : Polynomial K) ∣
        Polynomial.X ^
          (smithConformalRawExponent 2 2 d +
            10 * base (smithAxisProjection d)) :=
    polynomial_X_pow_dvd_X_pow_of_le 4 _ hfour
  have hout :=
    dvd_trans hsmall htotal
  simpa [smithConformalMultiplier,
    smithConformalMultiplierExponent] using hout

/-! ## Coefficients of the integral Smith family -/

/-- On an exponent in the source support, the explicit Smith family has the
chosen quotient coefficient. -/
theorem coeff_integralSmithConformalFamily_of_mem
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (integralSmithConformalFamily
          theta1 theta2 P hdiv) =
      smithConformalCoefficientQuotient
        theta1 theta2 P hdiv d := by
  classical
  unfold integralSmithConformalFamily
  simp [MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, hd]

/-- The integral Smith transform introduces no new source monomials. -/
theorem support_integralSmithConformalFamily_subset
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    (integralSmithConformalFamily
      theta1 theta2 P hdiv).support ⊆
        P.support := by
  intro d hdQ
  by_contra hnot
  have hcoeffzero :
      MvPolynomial.coeff d
          (integralSmithConformalFamily
            theta1 theta2 P hdiv) = 0 := by
    classical
    unfold integralSmithConformalFamily
    simp [MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hnot]
  exact
    (MvPolynomial.mem_support_iff.mp hdQ)
      hcoeffzero

/-! ## One extra power survives the conformal normalisation -/

/-- A strict symmetric improvement leaves one common parameter factor in
the normalised Smith family. -/
theorem strictSymmetricImprovement_commonParameterFactor
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase :
      HasSmithCoefficientOrderLowerBound
        base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    (hsmith :
      HasIntegralSmithConformalCoefficientDivisibility
        2 2
        (parameterRamificationFamily
          (K := K) 10 P)) :
    HasCommonParameterFactor
      1
      (integralSmithConformalFamily
        2 2
        (parameterRamificationFamily
          (K := K) 10 P)
        hsmith) := by
  let Pram :=
    parameterRamificationFamily
      (K := K) 10 P
  let Q :=
    integralSmithConformalFamily
      2 2 Pram hsmith
  have hram :=
    smithCoefficientOrderLowerBound_after_ramification_ten
      (K := K) base P hbase
  intro d hdQ
  have hdRam :
      d ∈ Pram.support :=
    support_integralSmithConformalFamily_subset
      2 2 Pram hsmith hdQ
  have hdP :
      d ∈ P.support :=
    (MvPolynomial.support_map_subset
      (parameterRamificationHom (K := K) 10)
      P) hdRam
  have hcoeff :
      Polynomial.X ^
          (10 * base (smithAxisProjection d)) ∣
        MvPolynomial.coeff d Pram := by
    exact hram d hdRam
  have hfive :
      5 ≤
        smithConformalRawExponent 2 2 d +
          10 * base (smithAxisProjection d) :=
    strictSymmetricImprovement_raw_plus_base_ge_five
      (K := K) base P hstrict hdP
  have hfactor :
      smithConformalCoefficientFactor
          (K := K) 2 2 d =
        Polynomial.X ^
          smithConformalRawExponent 2 2 d :=
    smithConformalCoefficientFactor_two_two (K := K) d
  have htotal :
      Polynomial.X ^
          (smithConformalRawExponent 2 2 d +
            10 * base (smithAxisProjection d)) ∣
        smithConformalCoefficientFactor
            (K := K) 2 2 d *
          MvPolynomial.coeff d Pram := by
    rcases hcoeff with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [hfactor, hr]
    calc
      Polynomial.X ^
            smithConformalRawExponent 2 2 d *
          (Polynomial.X ^
              (10 * base (smithAxisProjection d)) *
            r) =
        (Polynomial.X ^
            smithConformalRawExponent 2 2 d *
          Polynomial.X ^
            (10 * base (smithAxisProjection d))) *
          r := by ring
      _ =
        Polynomial.X ^
            (smithConformalRawExponent 2 2 d +
              10 * base (smithAxisProjection d)) *
          r := by
            rw [← pow_add]
  have hfivePow :
      (Polynomial.X ^ 5 : Polynomial K) ∣
        Polynomial.X ^
          (smithConformalRawExponent 2 2 d +
            10 * base (smithAxisProjection d)) :=
    polynomial_X_pow_dvd_X_pow_of_le
      (K := K) 5 _ hfive
  have hfiveLeft :
      (Polynomial.X ^ 5 : Polynomial K) ∣
        smithConformalCoefficientFactor
            (K := K) 2 2 d *
          MvPolynomial.coeff d Pram :=
    dvd_trans hfivePow htotal
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      2 2 Pram hsmith hdRam
  have hquotFiveRaw :
      (Polynomial.X ^ 5 : Polynomial K) ∣
        smithConformalMultiplier
            (K := K) 2 2 *
          smithConformalCoefficientQuotient
            2 2 Pram hsmith d := by
    rw [← hspec]
    exact hfiveLeft
  have hquotFive :
      (Polynomial.X ^ 5 : Polynomial K) ∣
        Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient
            2 2 Pram hsmith d := by
    simpa [smithConformalMultiplier,
      smithConformalMultiplierExponent] using
      hquotFiveRaw
  have hXquot :
      Polynomial.X ∣
        smithConformalCoefficientQuotient
          2 2 Pram hsmith d := by
    simpa using
      polynomial_X_dvd_of_succ_pow_dvd_pow_mul
        (K := K)
        4
        (smithConformalCoefficientQuotient
          2 2 Pram hsmith d)
        hquotFive
  rw [coeff_integralSmithConformalFamily_of_mem
    2 2 Pram hsmith hdRam]
  simpa using hXquot

/-! ## Moving-section denominator clearing -/

/-- A moving section is axis-adapted when each transverse coordinate has at
least one parameter factor. -/
def HasSmithTransverseParameterFactor
    (a : Fin 4 → Polynomial K) : Prop :=
  Polynomial.X ∣ a 1 ∧
  Polynomial.X ∣ a 2 ∧
  Polynomial.X ∣ a 3

/-- The fixed ramification by ten makes an axis-adapted moving section
integral for the inverse `(2,2)` Smith source change. -/
theorem smithTransverseParameterFactor_ramified_integralSection
    (a : Fin 4 → Polynomial K)
    (haxis :
      HasSmithTransverseParameterFactor a) :
    HasIntegralSmithConformalSectionDivisibility
      2 2
      (parameterRamificationSection
        (K := K) 10 a) := by
  intro i
  fin_cases i
  · simp [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent]
  · have hx1 :
        (Polynomial.X ^ 1 : Polynomial K) ∣ a 1 := by
      simpa using haxis.1
    have h10 :=
      parameterRamification_pow_dvd
        (K := K) 10 1 (a 1) hx1
    have h2 :
        (Polynomial.X ^ 2 : Polynomial K) ∣
          Polynomial.X ^ 10 :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) 2 10 (by omega)
    simpa [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent,
      parameterRamificationSection] using
      dvd_trans h2 h10
  · have hx1 :
        (Polynomial.X ^ 1 : Polynomial K) ∣ a 2 := by
      simpa using haxis.2.1
    have h10 :=
      parameterRamification_pow_dvd
        (K := K) 10 1 (a 2) hx1
    have h2 :
        (Polynomial.X ^ 2 : Polynomial K) ∣
          Polynomial.X ^ 10 :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) 2 10 (by omega)
    simpa [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent,
      parameterRamificationSection] using
      dvd_trans h2 h10
  · have hx1 :
        (Polynomial.X ^ 1 : Polynomial K) ∣ a 3 := by
      simpa using haxis.2.2
    have h10 :=
      parameterRamification_pow_dvd
        (K := K) 10 1 (a 3) hx1
    have h4 :
        (Polynomial.X ^ 4 : Polynomial K) ∣
          Polynomial.X ^ 10 :=
      polynomial_X_pow_dvd_X_pow_of_le
        (K := K) 4 10 (by omega)
    simpa [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent,
      parameterRamificationSection] using
      dvd_trans h4 h10

/-! ## End-to-end complementary Smith restart -/

/-- **Strict symmetric Smith improvement gives a strict global restart on
the fixed ramified scale.**

The state defect is measured after the once-for-all degree-ten
ramification.  The sequence is:

1. ramify the family and sections by `10`;
2. perform the integral `(2,2)` Smith conformal move;
3. preserve exact family-gradient collision;
4. observe one common parameter factor;
5. remove it and drop the defect by exactly `4`.
-/
theorem strictSymmetricImprovement_exactCollision_and_strictRestart
    {s : GlobalRestartState}
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase :
      HasSmithCoefficientOrderLowerBound
        base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (a b : Fin 4 → Polynomial K)
    (haaxis :
      HasSmithTransverseParameterFactor a)
    (hbaxis :
      HasSmithTransverseParameterFactor b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hs :
      s.defect = 10 * Delta)
    (newRepair : RepairState) :
    let Pram :=
      parameterRamificationFamily
        (K := K) 10 P
    let hsmith :=
      strictSymmetricImprovement_integralSmithDivisibility
        (K := K) base P hbase hstrict
    let Psmith :=
      integralSmithConformalFamily
        2 2 Pram hsmith
    let hcommon :=
      strictSymmetricImprovement_commonParameterFactor
        (K := K) base P hbase hstrict hsmith
    let Q :=
      commonParameterFactorFamily
        1 Psmith hcommon
    let t : GlobalRestartState :=
      { defect := 10 * Delta - 4
        repair := newRepair }
    HasPolynomialFamilyHessianDefect
        (K := K) Q (10 * Delta - 4) ∧
      HasPolynomialFamilyExactGradientCollision
        Q
        (integralSmithConformalSection
          2 2
          (parameterRamificationSection
            (K := K) 10 a)
          (smithTransverseParameterFactor_ramified_integralSection
            (K := K) a haaxis))
        (integralSmithConformalSection
          2 2
          (parameterRamificationSection
            (K := K) 10 b)
          (smithTransverseParameterFactor_ramified_integralSection
            (K := K) b hbaxis)) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  dsimp
  let Pram :=
    parameterRamificationFamily
      (K := K) 10 P
  let hsmith :=
    strictSymmetricImprovement_integralSmithDivisibility
      base P hbase hstrict
  let Psmith :=
    integralSmithConformalFamily
      2 2 Pram hsmith
  let hcommon :=
    strictSymmetricImprovement_commonParameterFactor
      base P hbase hstrict hsmith
  let aram :=
    parameterRamificationSection
      (K := K) 10 a
  let bram :=
    parameterRamificationSection
      (K := K) 10 b
  let hadiv :=
    smithTransverseParameterFactor_ramified_integralSection
      (K := K) a haaxis
  let hbdiv :=
    smithTransverseParameterFactor_ramified_integralSection
      (K := K) b hbaxis
  let asmith :=
    integralSmithConformalSection
      2 2 aram hadiv
  let bsmith :=
    integralSmithConformalSection
      2 2 bram hbdiv
  have hramDef :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (10 * Delta) := by
    dsimp [Pram]
    exact
      parameterRamificationFamily_hasHessianDefect
        10 Delta P hdef
  have hsmithDef :
      HasPolynomialFamilyHessianDefect
        (K := K) Psmith (10 * Delta) := by
    dsimp [Psmith, hsmith, Pram]
    exact
      integralSmithConformalFamily_preservesHessianDefect
        2 2 (10 * Delta) Pram hsmith hramDef
  have hramColl :
      HasPolynomialFamilyExactGradientCollision
        Pram aram bram := by
    dsimp [Pram, aram, bram]
    exact
      polynomialFamilyExactGradientCollision_parameterRamification
        10 P a b hcoll
  have hsmithColl :
      HasPolynomialFamilyExactGradientCollision
        Psmith asmith bsmith := by
    dsimp [Psmith, asmith, bsmith, hsmith,
      aram, bram, hadiv, hbdiv, Pram]
    exact
      polynomialFamilyExactGradientCollision_integralSmithConformal
        2 2 Pram hsmith aram bram hadiv hbdiv
        hramColl
  have hout :=
    commonParameterFactor_one_exactCollision_and_strictRestart
      (s := s)
      Psmith hcommon hsmithDef
      asmith bsmith hsmithColl
      hs newRepair
  simpa [Pram, hsmith, Psmith, hcommon,
    aram, bram, hadiv, hbdiv, asmith, bsmith]
    using hout

end

end HC4.Valuation
