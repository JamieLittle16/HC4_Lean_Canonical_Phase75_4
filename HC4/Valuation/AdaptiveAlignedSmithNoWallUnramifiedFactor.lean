import HC4.Valuation.AdaptiveAlignedSmithNoWallUnramifiedSmith
import Mathlib.Tactic

/-!
# A18.4.57: the lower no-wall Smith family has common factor X^m

A18.4.56 constructs the no-wall Smith move directly on the original parameter
scale.  Let `m` be the least exact parameter order among the zero Smith-grade
source coefficients.

After the lower `(m,m)` conformal normalisation every coefficient has one
further factor `X^m`:

* at Smith grade zero the source half-degree is exactly two, so the conformal
  multiplier cancels the source factor and minimality supplies `X^m` from the
  original coefficient;
* at positive Smith grade, parity makes the grade at least two, hence the
  source half-degree is at least three and the conformal source factor itself
  supplies the extra `X^m`.

Thus the lower Smith family has a common factor `X^m`.  Removing it lowers the
four-dimensional Hessian defect by exactly `4m`, with no change of parameter
scale and with the exact gradient collision preserved.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Smith grade zero is exactly half source degree two. -/
theorem noWallSmithSourceDegree_eq_two_of_delta_zero
    (d : Fin 4 →₀ ℕ)
    (hz : smithSeparatorDelta 1 1 (smithAxisProjection d) = 0) :
    noWallSmithSourceDegree d = 2 := by
  have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
  rw [smithConformalRawExponent_two_two_eq_two_mul_noWallDegree] at hrel
  rw [hz] at hrel
  have hz' :
      (2 : ℤ) * (noWallSmithSourceDegree d : ℤ) = 4 := by
    omega
  exact_mod_cast (by omega : noWallSmithSourceDegree d = 2)

/-- A nonzero nonnegative Smith grade has half source degree at least three. -/
theorem three_le_noWallSmithSourceDegree_of_delta_pos
    (d : Fin 4 →₀ ℕ)
    (hnonneg : 0 ≤ smithSeparatorDelta 1 1 (smithAxisProjection d))
    (hne : smithSeparatorDelta 1 1 (smithAxisProjection d) ≠ 0) :
    3 ≤ noWallSmithSourceDegree d := by
  have hdelta2 :=
    smithSeparatorDelta_one_one_ge_two_of_nonnegative_ne_zero
      (smithAxisProjection d) hnonneg hne
  have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
  rw [smithConformalRawExponent_two_two_eq_two_mul_noWallDegree] at hrel
  rw [hrel] at hdelta2
  exact_mod_cast (by omega : (3 : ℤ) ≤ (noWallSmithSourceDegree d : ℤ))

/-- The unramified lower Smith family contains the common factor selected by
the minimal zero-grade coefficient order. -/
theorem noWall_unramifiedSmith_commonFactor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b) :
    let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b Delta hdef hnone
    let m := minimalZeroSmithParameterOrder P hne
    let hsmith :=
      noWall_unramifiedSmith_coefficientDivisibility
        (K := K) P (zeroPolynomialSection (K := K)) b hnone m
    HasCommonParameterFactor m
      (integralSmithConformalFamily m m P hsmith) := by
  dsimp only
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let hsmith :=
    noWall_unramifiedSmith_coefficientDivisibility
      (K := K) P (zeroPolynomialSection (K := K)) b hnone m
  let Q := integralSmithConformalFamily m m P hsmith
  intro d hdQ
  have hdP : d ∈ P.support :=
    support_integralSmithConformalFamily_subset m m P hsmith hdQ
  have hnonneg :=
    no_negativeSmithDerivative_of_noGenuineWall
      P (zeroPolynomialSection (K := K)) b hnone d hdP
  let q := smithConformalCoefficientQuotient m m P hsmith d
  have hspec :
      smithConformalCoefficientFactor (K := K) m m d *
          MvPolynomial.coeff d P =
        smithConformalMultiplier (K := K) m m * q := by
    simpa [q] using
      smithConformalCoefficientQuotient_spec_of_mem m m P hsmith hdP

  have htotal :
      (Polynomial.X ^ (2 * m + m) : Polynomial K) ∣
        smithConformalCoefficientFactor (K := K) m m d *
          MvPolynomial.coeff d P := by
    by_cases hz :
        smithSeparatorDelta 1 1 (smithAxisProjection d) = 0
    · have hdeg : noWallSmithSourceDegree d = 2 :=
        noWallSmithSourceDegree_eq_two_of_delta_zero d hz
      have hd0 : d ∈ zeroSmithSourceSupport P :=
        (mem_zeroSmithSourceSupport P).2 ⟨hdP, hz⟩
      have hmle : m ≤ smithFamilyCoefficientOrder P d := by
        simpa [m, hne] using
          minimalZeroSmithParameterOrder_le P hne hd0
      have hvdiv :
          Polynomial.X ^ (smithFamilyCoefficientOrder P d) ∣
            MvPolynomial.coeff d P :=
        smithFamilyCoefficientOrder_dvd P hdP
      have hmPow :
          (Polynomial.X ^ m : Polynomial K) ∣
            Polynomial.X ^ (smithFamilyCoefficientOrder P d) :=
        polynomial_X_pow_dvd_X_pow_of_le (K := K) _ _ hmle
      have hmCoeff :
          (Polynomial.X ^ m : Polynomial K) ∣
            MvPolynomial.coeff d P :=
        dvd_trans hmPow hvdiv
      rcases hmCoeff with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [smithConformalCoefficientFactor_diag_eq, hdeg, hr]
      have hexp : m * 2 = 2 * m := by omega
      rw [hexp, ← pow_add]
      rfl
    · have hdeg : 3 ≤ noWallSmithSourceDegree d :=
        three_le_noWallSmithSourceDegree_of_delta_pos d hnonneg hz
      have hexp : 2 * m + m ≤ m * noWallSmithSourceDegree d := by
        nlinarith
      have hpow :
          (Polynomial.X ^ (2 * m + m) : Polynomial K) ∣
            Polynomial.X ^ (m * noWallSmithSourceDegree d) :=
        polynomial_X_pow_dvd_X_pow_of_le (K := K) _ _ hexp
      rw [smithConformalCoefficientFactor_diag_eq]
      exact dvd_mul_of_dvd_left hpow _

  have hquotRaw :
      (Polynomial.X ^ (2 * m + m) : Polynomial K) ∣
        Polynomial.X ^ (2 * m) * q := by
    rw [← smithConformalMultiplier_diag (K := K) m]
    rw [← hspec]
    exact htotal
  have hq : (Polynomial.X ^ m : Polynomial K) ∣ q :=
    polynomial_X_pow_dvd_of_add_pow_dvd_pow_mul
      (K := K) (2 * m) m q hquotRaw
  dsimp [Q]
  rw [coeff_integralSmithConformalFamily_of_mem m m P hsmith hdP]
  simpa [q] using hq

/-- Lower-scale no-wall primitive package after the common factor is removed. -/
structure AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
    (degreeCap Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K) : Type (u + 1) where
  noWall :
    ¬ HasAlignedSmithGenuineWall
      P (zeroPolynomialSection (K := K)) b
  hessianDefect : HasPolynomialFamilyHessianDefect (K := K) P Delta
  nonlinearDegreeBound : NonlinearDegreeBound degreeCap P
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      P (zeroPolynomialSection (K := K)) b
  sectionSpecial :
    polynomialSectionSpecialPoint b =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  zeroSupport : (zeroSmithSourceSupport P).Nonempty
  m : ℕ
  m_eq : m = minimalZeroSmithParameterOrder P zeroSupport
  smithData :
    AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b
  commonFactor : HasCommonParameterFactor m smithData.smithFamily

namespace AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData

noncomputable def reducedFamily
    {degreeCap Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData degreeCap Delta P b) :=
  commonParameterFactorFamily D.m D.smithData.smithFamily D.commonFactor

/-- Exact lower defect after the unramified common-factor extraction. -/
theorem reducedFamily_hessianDefect
    {degreeCap Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData degreeCap Delta P b) :
    HasPolynomialFamilyHessianDefect
      (K := K) D.reducedFamily (Delta - 4 * D.m) := by
  exact commonParameterFactor_hasHessianDefect_sub_four_mul
    D.m D.smithData.smithFamily D.commonFactor Delta
    D.smithData.smithFamily_hessianDefect

/-- The nonlinear source degree ceiling survives the extraction. -/
theorem reducedFamily_nonlinearDegreeBound
    {degreeCap Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData degreeCap Delta P b) :
    NonlinearDegreeBound degreeCap D.reducedFamily := by
  exact nonlinearDegreeBound_commonParameterFactor
    degreeCap D.m D.smithData.smithFamily
    D.smithData.smithFamily_nonlinearDegreeBound D.commonFactor

/-- The exact collision survives common-factor removal. -/
theorem reducedFamily_exactCollision
    {degreeCap Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData degreeCap Delta P b) :
    HasPolynomialFamilyExactGradientCollision
      D.reducedFamily (zeroPolynomialSection (K := K))
        D.smithData.smithRightSection := by
  exact polynomialFamilyExactGradientCollision_commonParameterFactor
    D.m D.smithData.smithFamily D.commonFactor
    (zeroPolynomialSection (K := K)) D.smithData.smithRightSection
    D.smithData.smithFamily_exactCollision

/-- Canonical package using the least zero-grade coefficient order. -/
noncomputable def ofNoWall
    (degreeCap Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hdegree : NonlinearDegreeBound degreeCap P)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData degreeCap Delta P b := by
  let hne :=
    zeroSmithSourceSupport_nonempty_of_noGenuineWall
      P (zeroPolynomialSection (K := K)) b Delta hdef hnone
  let m := minimalZeroSmithParameterOrder P hne
  let S := AdaptiveAlignedSmithNoWallUnramifiedSmithData.ofNoWall
    degreeCap Delta m P b hnone hdef hdegree hcoll hb
  have hcommon : HasCommonParameterFactor m S.smithFamily := by
    simpa [S, m, hne] using
      noWall_unramifiedSmith_commonFactor
        (K := K) P b Delta hdef hnone
  exact {
    noWall := hnone
    hessianDefect := hdef
    nonlinearDegreeBound := hdegree
    exactCollision := hcoll
    sectionSpecial := hb
    zeroSupport := hne
    m := m
    m_eq := rfl
    smithData := S
    commonFactor := hcommon
  }

end AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData

end

end HC4.Valuation
