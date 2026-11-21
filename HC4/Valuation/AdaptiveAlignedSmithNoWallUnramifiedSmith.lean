import HC4.Valuation.AdaptiveAlignedSmithCanonicalDirectFirstContactDispatcher
import HC4.Valuation.PrimitiveSmithEndpoint
import Mathlib.Tactic

/-!
# A18.4.56: the no-wall Smith move already exists before ramification

The historical primitive endpoint performs one fixed ramification by `20`,
then a Smith move with parameters `(20m,20m)`, then removes the common factor
`X^(20m)`.  All three exponents are multiples of `20`.

The underlying reason is stronger: when there is no genuine aligned Smith
wall, every supported source monomial has nonnegative symmetric Smith grade.
Consequently the conformal move with the *unramified* parameters `(m,m)` is
already integral on the original family.  The no-wall theorem also says both
marked sections are axial, so their inverse source change is integral as well.

This file packages that lower-scale Smith transform and proves that it keeps
exactly the original Hessian clock, nonlinear degree bound and gradient
collision.  The next patch extracts its common factor `X^m`; that will turn
the old 20-fold clock loss into an ordinary natural-number defect drop.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Half of the raw symmetric Smith source exponent. -/
def noWallSmithSourceDegree (d : Fin 4 →₀ ℕ) : ℕ :=
  d 1 + d 2 + 2 * d 3

@[simp]
theorem smithConformalRawExponent_two_two_eq_two_mul_noWallDegree
    (d : Fin 4 →₀ ℕ) :
    smithConformalRawExponent 2 2 d =
      2 * noWallSmithSourceDegree d := by
  unfold smithConformalRawExponent noWallSmithSourceDegree
  ring

/-- Nonnegative symmetric Smith grade means the half source degree is at
least two. -/
theorem two_le_noWallSmithSourceDegree_of_delta_nonnegative
    (d : Fin 4 →₀ ℕ)
    (hdelta :
      0 ≤ smithSeparatorDelta 1 1 (smithAxisProjection d)) :
    2 ≤ noWallSmithSourceDegree d := by
  have hrel := smithSeparatorDelta_projection_eq_raw_sub_four d
  rw [smithConformalRawExponent_two_two_eq_two_mul_noWallDegree] at hrel
  rw [hrel] at hdelta
  exact_mod_cast (by omega : (2 : ℤ) ≤ (noWallSmithSourceDegree d : ℤ))

/-- At equal Smith parameters `(m,m)`, the coefficient factor is exactly the
pure parameter power indexed by the half source degree. -/
theorem smithConformalCoefficientFactor_diag_eq
    (m : ℕ)
    (d : Fin 4 →₀ ℕ) :
    smithConformalCoefficientFactor (K := K) m m d =
      Polynomial.X ^ (m * noWallSmithSourceDegree d) := by
  unfold smithConformalCoefficientFactor
  rw [Fin.prod_univ_four]
  simp [smithConformalDerivativeCoefficient,
    smithConformalSourceExponent, noWallSmithSourceDegree,
    pow_add, ← pow_mul]
  congr 1
  ring

@[simp]
theorem smithConformalMultiplier_diag
    (m : ℕ) :
    smithConformalMultiplier (K := K) m m =
      Polynomial.X ^ (2 * m) := by
  simp [smithConformalMultiplier,
    smithConformalMultiplierExponent]
  congr 1
  omega

/-- No genuine wall is already enough for coefficient integrality of the
unramified `(m,m)` conformal move, for every `m`. -/
theorem noWall_unramifiedSmith_coefficientDivisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hnone : ¬ HasAlignedSmithGenuineWall P a b)
    (m : ℕ) :
    HasIntegralSmithConformalCoefficientDivisibility m m P := by
  intro d hd
  have hdelta :=
    no_negativeSmithDerivative_of_noGenuineWall P a b hnone d hd
  have hdeg : 2 ≤ noWallSmithSourceDegree d :=
    two_le_noWallSmithSourceDegree_of_delta_nonnegative d hdelta
  have hexp : 2 * m ≤ m * noWallSmithSourceDegree d := by
    nlinarith
  have hpow :
      (Polynomial.X ^ (2 * m) : Polynomial K) ∣
        Polynomial.X ^ (m * noWallSmithSourceDegree d) :=
    polynomial_X_pow_dvd_X_pow_of_le (K := K) _ _ hexp
  rw [smithConformalCoefficientFactor_diag_eq,
    smithConformalMultiplier_diag]
  exact dvd_mul_of_dvd_left hpow _

/-- The zero marked section is integral for every diagonal Smith move. -/
theorem zeroSection_unramifiedSmith_divisibility
    (m : ℕ) :
    HasIntegralSmithConformalSectionDivisibility
      (K := K) m m (zeroPolynomialSection (K := K)) := by
  intro i
  simp [smithConformalDerivativeCoefficient,
    smithConformalSourceExponent, zeroPolynomialSection]

/-- In the no-wall branch the right marked section is axial, so the lower
`(m,m)` inverse source change is integral without ramification. -/
theorem noWall_rightSection_unramifiedSmith_divisibility
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (m : ℕ) :
    HasIntegralSmithConformalSectionDivisibility (K := K) m m b := by
  intro i
  by_cases hi : i = (0 : Fin 4)
  · subst i
    simp [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent]
  · have hz :=
      rightTransverse_zero_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b hnone i hi
    rw [hz]
    exact dvd_zero _

/-- The chosen integral inverse image of the zero section is necessarily the
zero section itself. -/
theorem integralSmithConformalSection_zero
    (m : ℕ) :
    integralSmithConformalSection
        (K := K) m m (zeroPolynomialSection (K := K))
        (zeroSection_unramifiedSmith_divisibility (K := K) m) =
      zeroPolynomialSection (K := K) := by
  funext i
  have hinflate := congrFun
    (smithConformalInflateSection_integralSection_eq
      m m (zeroPolynomialSection (K := K))
      (zeroSection_unramifiedSmith_divisibility (K := K) m)) i
  change
    smithConformalDerivativeCoefficient (K := K) m m i *
        integralSmithConformalSection
          m m (zeroPolynomialSection (K := K))
          (zeroSection_unramifiedSmith_divisibility (K := K) m) i = 0
    at hinflate
  have hcoeff :
      smithConformalDerivativeCoefficient (K := K) m m i ≠ 0 := by
    unfold smithConformalDerivativeCoefficient
    exact pow_ne_zero _ Polynomial.X_ne_zero
  exact (mul_eq_zero.mp hinflate).resolve_left hcoeff

/-- Lower-scale no-wall Smith data before extracting the common factor. -/
structure AdaptiveAlignedSmithNoWallUnramifiedSmithData
    (degreeCap Delta m : ℕ)
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
  coefficientDivisibility :
    HasIntegralSmithConformalCoefficientDivisibility m m P
  rightSectionDivisibility :
    HasIntegralSmithConformalSectionDivisibility (K := K) m m b

namespace AdaptiveAlignedSmithNoWallUnramifiedSmithData

/-- The actual unramified Smith family. -/
noncomputable def smithFamily
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :=
  integralSmithConformalFamily m m P D.coefficientDivisibility

/-- The transformed right marked section. -/
noncomputable def smithRightSection
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :=
  integralSmithConformalSection m m b D.rightSectionDivisibility

/-- The lower Smith family still has determinant clock exactly `Delta`. -/
theorem smithFamily_hessianDefect
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :
    HasPolynomialFamilyHessianDefect (K := K) D.smithFamily Delta := by
  exact integralSmithConformalFamily_preservesHessianDefect
    m m Delta P D.coefficientDivisibility D.hessianDefect

/-- No nonlinear source degree is introduced. -/
theorem smithFamily_nonlinearDegreeBound
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :
    NonlinearDegreeBound degreeCap D.smithFamily := by
  exact nonlinearDegreeBound_integralSmithConformal
    degreeCap m m P D.nonlinearDegreeBound D.coefficientDivisibility

/-- The exact gradient collision survives on the lower Smith family. -/
theorem smithFamily_exactCollision
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :
    HasPolynomialFamilyExactGradientCollision
      D.smithFamily (zeroPolynomialSection (K := K)) D.smithRightSection := by
  have h := polynomialFamilyExactGradientCollision_integralSmithConformal
    m m P D.coefficientDivisibility
    (zeroPolynomialSection (K := K)) b
    (zeroSection_unramifiedSmith_divisibility (K := K) m)
    D.rightSectionDivisibility D.exactCollision
  rw [integralSmithConformalSection_zero] at h
  exact h

/-- Canonical data constructor from the no-wall hypotheses. -/
noncomputable def ofNoWall
    (degreeCap Delta m : ℕ)
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
    AdaptiveAlignedSmithNoWallUnramifiedSmithData degreeCap Delta m P b := {
  noWall := hnone
  hessianDefect := hdef
  nonlinearDegreeBound := hdegree
  exactCollision := hcoll
  sectionSpecial := hb
  coefficientDivisibility :=
    noWall_unramifiedSmith_coefficientDivisibility
      P (zeroPolynomialSection (K := K)) b hnone m
  rightSectionDivisibility :=
    noWall_rightSection_unramifiedSmith_divisibility P b hnone m
}

end AdaptiveAlignedSmithNoWallUnramifiedSmithData

end

end HC4.Valuation
