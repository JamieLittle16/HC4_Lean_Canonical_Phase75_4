import HC4.Valuation.SmithConformalCovariance
import HC4.Valuation.SymmetricSmithImprovementRestart
import HC4.Valuation.DefectRetainingDepartureFrontier
import HC4.Newton.SmithRefinedFacePolynomial
import Mathlib.Tactic

/-!
# Canonical Smith-Rees deformation of the special fibre

The determinant-defect parameter of a polynomial family and the Smith
separator parameter are different filtrations.  This file constructs the
second one honestly.

For a field-valued special fibre `F`, embed its coefficients as constant
polynomials and apply the already-green integral Smith conformal transform
with parameters `(2,2)`.  The exponent left after dividing by the conformal
multiplier is exactly the symmetric Smith separator derivative
`smithSeparatorDelta 1 1`.

Consequently, whenever that derivative is nonnegative on the support, the
normalised transformation is integral.  More importantly, its special fibre
is *exactly* the canonical symmetric Smith subface polynomial.  Thus the
rank-one persistent packet retained by the lossless frontier is realised as
an actual special fibre of an honest Rees family rather than identified with
the unrelated constant layer of the original DVR family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Embed a field-valued polynomial as a family constant in the Rees
parameter. -/
noncomputable def constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.map Polynomial.C F

@[simp] theorem coeff_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (constantPolynomialFamily F) =
      Polynomial.C (MvPolynomial.coeff d F) := by
  unfold constantPolynomialFamily
  rw [MvPolynomial.coeff_map]

/-- A support monomial of the constant family is a support monomial of the
underlying field-valued polynomial. -/
theorem mem_support_of_mem_constantPolynomialFamily_support
    (F : MvPolynomial (Fin 4) K)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (constantPolynomialFamily F).support) :
    d ∈ F.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hzero
  have hfamily := MvPolynomial.mem_support_iff.mp hd
  apply hfamily
  rw [coeff_constantPolynomialFamily, hzero]
  simp

/-- For the canonical symmetric Smith direction `(2,2)`, the exponent left
after the conformal multiplier is exactly the already-formalised symmetric
Smith separator derivative. -/
theorem canonicalSmith_rawExponent_sub_four_eq_separatorDelta
    (d : Fin 4 →₀ ℕ) :
    (smithConformalRawExponent 2 2 d : ℤ) - 4 =
      smithSeparatorDelta 1 1
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
  unfold smithSeparatorDelta
  rw [smithExtremeSeparator_one_one]
  unfold SmithSupportExponent.grade smithSupportExponentOf
    smithGradeDot smithGrade smithGradeFirst smithGradeSecond
    smithConformalRawExponent
  push_cast
  ring

/-- Nonnegative symmetric Smith derivative is exactly the integrality
inequality needed to divide the honest source inflation by `X^4`. -/
theorem four_le_canonicalSmith_rawExponent
    (d : Fin 4 →₀ ℕ)
    (hdelta :
      0 ≤ smithSeparatorDelta 1 1
        (smithSupportExponentOf (1 : Fin 4) 2 3 d)) :
    4 ≤ smithConformalRawExponent 2 2 d := by
  have h := canonicalSmith_rawExponent_sub_four_eq_separatorDelta d
  omega

/-- Coefficientwise integrality of the canonical Smith-Rees deformation.
Only nonnegativity of the symmetric separator on the actual support is
required. -/
theorem constantFamily_hasIntegralCanonicalSmithConformalDivisibility
    (F : MvPolynomial (Fin 4) K)
    (hdelta :
      ∀ d ∈ F.support,
        0 ≤ smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d)) :
    HasIntegralSmithConformalCoefficientDivisibility
      (K := K) 2 2 (constantPolynomialFamily F) := by
  intro d hd
  have hdF :=
    mem_support_of_mem_constantPolynomialFamily_support F hd
  have hle : 4 ≤ smithConformalRawExponent 2 2 d :=
    four_le_canonicalSmith_rawExponent d (hdelta d hdF)
  rw [smithConformalMultiplier]
  simp only [smithConformalMultiplierExponent]
  rw [smithConformalCoefficientFactor_two_two]
  rw [coeff_constantPolynomialFamily]
  refine
    ⟨Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4) *
        Polynomial.C (MvPolynomial.coeff d F), ?_⟩
  have hpow :
      (Polynomial.X : Polynomial K) ^ smithConformalRawExponent 2 2 d =
        (Polynomial.X : Polynomial K) ^ 4 *
          (Polynomial.X : Polynomial K) ^ (smithConformalRawExponent 2 2 d - 4) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    Polynomial.X ^ smithConformalRawExponent 2 2 d *
          Polynomial.C (MvPolynomial.coeff d F) =
        (Polynomial.X ^ 4 *
            Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4)) *
          Polynomial.C (MvPolynomial.coeff d F) := by
      rw [hpow]
    _ = Polynomial.X ^ 4 *
          (Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4) *
            Polynomial.C (MvPolynomial.coeff d F)) := by
      rw [mul_assoc]
    _ = Polynomial.X ^ (2 + 2) *
          (Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4) *
            Polynomial.C (MvPolynomial.coeff d F)) := by
      norm_num

/-- The canonical integral Smith-Rees family of a field-valued special
fibre. -/
noncomputable def canonicalSmithReesFamily
    (F : MvPolynomial (Fin 4) K)
    (hdelta :
      ∀ d ∈ F.support,
        0 ≤ smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  integralSmithConformalFamily
    2 2
    (constantPolynomialFamily F)
    (constantFamily_hasIntegralCanonicalSmithConformalDivisibility
      F hdelta)

/-- Coefficients of an integral Smith conformal family are exactly the
chosen quotient coefficients. -/
theorem coeff_integralSmithConformalFamily
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (integralSmithConformalFamily theta1 theta2 P hdiv) =
      smithConformalCoefficientQuotient theta1 theta2 P hdiv d := by
  classical
  by_cases hd : d ∈ P.support
  · exact
      coeff_integralSmithConformalFamily_of_mem
        theta1 theta2 P hdiv hd
  · unfold integralSmithConformalFamily
    simp [MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hd,
      smithConformalCoefficientQuotient]

/-- On a supported monomial the chosen canonical Smith quotient has the
expected explicit form `X^(raw-4) * C(coeff)`.  This removes all dependence
on the arbitrary `Classical.choose` used by the general integral transform. -/
theorem canonicalSmithCoefficientQuotient_eq
    (F : MvPolynomial (Fin 4) K)
    (hdelta :
      ∀ d ∈ F.support,
        0 ≤ smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (constantPolynomialFamily F).support) :
    smithConformalCoefficientQuotient
        2 2
        (constantPolynomialFamily F)
        (constantFamily_hasIntegralCanonicalSmithConformalDivisibility
          F hdelta)
        d =
      Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4) *
        Polynomial.C (MvPolynomial.coeff d F) := by
  let hdiv :=
    constantFamily_hasIntegralCanonicalSmithConformalDivisibility
      (K := K) F hdelta
  have hspec :=
    smithConformalCoefficientQuotient_spec_of_mem
      (K := K) 2 2 (constantPolynomialFamily F) hdiv hd
  have hdF :=
    mem_support_of_mem_constantPolynomialFamily_support F hd
  have hle : 4 ≤ smithConformalRawExponent 2 2 d :=
    four_le_canonicalSmith_rawExponent d (hdelta d hdF)
  have hpow :
      (Polynomial.X : Polynomial K) ^ smithConformalRawExponent 2 2 d =
        (Polynomial.X : Polynomial K) ^ 4 *
          (Polynomial.X : Polynomial K) ^ (smithConformalRawExponent 2 2 d - 4) := by
    rw [← pow_add]
    congr 1
    omega
  rw [smithConformalCoefficientFactor_two_two,
    coeff_constantPolynomialFamily,
    smithConformalMultiplier] at hspec
  simp only [smithConformalMultiplierExponent] at hspec
  rw [hpow] at hspec
  have hmul :
      Polynomial.X ^ 4 *
          (Polynomial.X ^ (smithConformalRawExponent 2 2 d - 4) *
            Polynomial.C (MvPolynomial.coeff d F)) =
        Polynomial.X ^ 4 *
          smithConformalCoefficientQuotient
            2 2 (constantPolynomialFamily F) hdiv d := by
    simpa [mul_assoc] using hspec
  exact
    (mul_left_cancel₀ (pow_ne_zero 4 Polynomial.X_ne_zero) hmul).symm

/-- For a supported monomial, its coefficient in the special fibre of the
canonical Smith-Rees family is the original coefficient exactly on the
zero Smith separator face and is zero above that face. -/
theorem constantCoeff_canonicalSmithCoefficientQuotient
    (F : MvPolynomial (Fin 4) K)
    (hdelta :
      ∀ d ∈ F.support,
        0 ≤ smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d))
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (constantPolynomialFamily F).support) :
    Polynomial.constantCoeff
        (smithConformalCoefficientQuotient
          2 2
          (constantPolynomialFamily F)
          (constantFamily_hasIntegralCanonicalSmithConformalDivisibility
            F hdelta)
          d) =
      if smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) = 0
      then MvPolynomial.coeff d F
      else 0 := by
  rw [canonicalSmithCoefficientQuotient_eq
    (K := K) F hdelta hd]
  have hdF :=
    mem_support_of_mem_constantPolynomialFamily_support F hd
  have hnonneg := hdelta d hdF
  have hclock :=
    canonicalSmith_rawExponent_sub_four_eq_separatorDelta d
  by_cases hzero :
      smithSeparatorDelta 1 1
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) = 0
  · have hraw : smithConformalRawExponent 2 2 d = 4 := by
      omega
    simp [hzero, hraw]
  · have hraw : 0 < smithConformalRawExponent 2 2 d - 4 := by
      omega
    have hraw_ne : smithConformalRawExponent 2 2 d - 4 ≠ 0 :=
      Nat.ne_of_gt hraw
    simp [hzero]
    intro hz
    exact (hraw_ne hz.symm).elim

/-- **Exact special-fibre theorem for the canonical Smith-Rees family.**

The `T=0` fibre of the honest integral `(2,2)` conformal deformation is
exactly the canonical symmetric Smith subface polynomial already retained by
the lossless frontier.  This is the filtration bridge needed before applying
the Schur clock. -/
theorem polynomialFamilySpecialFiber_canonicalSmithReesFamily
    (F : MvPolynomial (Fin 4) K)
    (hdelta :
      ∀ d ∈ F.support,
        0 ≤ smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d)) :
    polynomialFamilySpecialFiber
        (canonicalSmithReesFamily F hdelta) =
      canonicalSpecialFiberSmithPolynomial F := by
  classical
  apply MvPolynomial.ext
  intro d
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.coeff_map]
  unfold canonicalSmithReesFamily
  rw [coeff_integralSmithConformalFamily]
  by_cases hdF : d ∈ F.support
  · have hdConst : d ∈ (constantPolynomialFamily F).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [coeff_constantPolynomialFamily]
      exact Polynomial.C_ne_zero.mpr
        (MvPolynomial.mem_support_iff.mp hdF)
    rw [constantCoeff_canonicalSmithCoefficientQuotient
      (K := K) F hdelta hdConst]
    unfold canonicalSpecialFiberSmithPolynomial
    rw [coeff_smithSubfacePolynomial]
    have hproj :
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
          smithProjectedSupport (1 : Fin 4) 2 3 F := by
      unfold smithProjectedSupport
      exact Finset.mem_image.mpr
        ⟨d, hdF, rfl⟩
    by_cases hzero :
        smithSeparatorDelta 1 1
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) = 0
    · have hmem :
          smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
            canonicalSpecialFiberSmithSubface F := by
        unfold canonicalSpecialFiberSmithSubface
        exact
          (mem_smithSymmetricBalancedSubface).2
            ⟨hproj, rfl, hzero⟩
      simp [hzero, hmem]
    · have hnot :
          smithSupportExponentOf (1 : Fin 4) 2 3 d ∉
            canonicalSpecialFiberSmithSubface F := by
        intro hmem
        unfold canonicalSpecialFiberSmithSubface at hmem
        exact hzero
          ((mem_smithSymmetricBalancedSubface).1 hmem).2.2
      simp [hzero, hnot]
  · have hdConst : d ∉ (constantPolynomialFamily F).support := by
      intro hmem
      exact hdF
        (mem_support_of_mem_constantPolynomialFamily_support F hmem)
    have hqzero :
        smithConformalCoefficientQuotient
            2 2
            (constantPolynomialFamily F)
            (constantFamily_hasIntegralCanonicalSmithConformalDivisibility
              F hdelta)
            d = 0 := by
      unfold smithConformalCoefficientQuotient
      simp [hdConst]
    rw [hqzero]
    simp
    unfold canonicalSpecialFiberSmithPolynomial
    rw [coeff_smithSubfacePolynomial]
    have hc0 : MvPolynomial.coeff d F = 0 := by
      by_contra hc
      exact hdF (MvPolynomial.mem_support_iff.mpr hc)
    simp [hc0]

end

end HC4.Valuation

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The retained nonzero persistent packet forces the homogeneous degree of
a lossless Smith frontier to be at least two.  This recovers the degree
hypothesis consumed by the collision-to-Smith shape theorem without adding a
new field to the frontier. -/
theorem CanonicalSmithLosslessFrontier.degree_two_le
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    2 ≤ D := by
  by_contra hD
  have hDlt : D < 2 := by omega
  let F := polynomialFamilySpecialFiber f.family
  let G := canonicalSpecialFiberSmithPolynomial F
  have hGhom : G.IsHomogeneous D := by
    unfold G canonicalSpecialFiberSmithPolynomial
    exact
      smithSubfacePolynomial_isHomogeneous
        (1 : Fin 4) 2 3
        (canonicalSpecialFiberSmithSubface F)
        f.specialHomogeneous
  apply f.packet_ne_zero
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_zero]
  by_contra hd
  have hpacket := f.persistentPacket d hd
  rcases hpacket with ⟨hx, hyz, hother⟩
  have hw : d (3 : Fin 4) = 0 :=
    hother 3
      (Ne.symm finFour_zero_ne_three)
      (Ne.symm finFour_one_ne_three)
      (Ne.symm finFour_two_ne_three)
  have hdeg :
      Finsupp.weight (fun _ : Fin 4 => 1) d = D :=
    hGhom hd
  have hdecomp :=
    finsupp_eq_fourCoordinateSum
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      d
  rw [hdecomp] at hdeg
  have htotal :
      d 0 + d 1 + d 2 + d 3 = D := by
    simpa [Finsupp.weight_single, add_assoc] using hdeg
  have hxzero : d 0 = 0 := by
    rw [hx]
    omega
  omega

/-- Every support monomial of the special fibre retained by a lossless
frontier has nonnegative symmetric Smith separator derivative.  This is the
precise integrality input for the canonical Smith-Rees deformation. -/
theorem CanonicalSmithLosslessFrontier.specialFiber_symmetricDelta_nonnegative
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    ∀ d ∈ (polynomialFamilySpecialFiber f.family).support,
      0 ≤ smithSeparatorDelta 1 1
        (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
  let F := polynomialFamilySpecialFiber f.family
  have hspecial :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
    dsimp [F]
    exact
      polynomialFamilyCollision_specialFiber_zero_axisZero
        f.family f.leftSection f.rightSection
        f.exactCollision f.leftSpecial f.rightSpecial
  have hshape :=
    homogeneous_exactAxisCollision_generalSurvivingSmithFaceShape
      (K := K)
      (0 : Fin 4) 1 2 3
      finFour_zero_ne_one
      finFour_zero_ne_two
      finFour_zero_ne_three
      finFour_one_ne_two
      finFour_one_ne_three
      finFour_two_ne_three
      finFour_standard_isFourCoordinateChart
      f.specialHomogeneous f.degree_two_le hspecial
      0 (fun _ => (0 : ℤ))
  intro d hd
  have he :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
        smithProjectedSupport (1 : Fin 4) 2 3 F := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  exact
    smithSeparatorDelta_one_one_nonnegative_of_generalShape
      _ (hshape _ he rfl)

/-- The canonical Smith-Rees family attached to a lossless frontier's
special fibre.  This parameter is the Smith separator parameter, not the
original determinant-defect parameter. -/
noncomputable def CanonicalSmithLosslessFrontier.smithReesFamily
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  canonicalSmithReesFamily
    (polynomialFamilySpecialFiber f.family)
    f.specialFiber_symmetricDelta_nonnegative

/-- **Frontier-to-Rees exposure theorem.**
The special fibre of the honest Smith-Rees deformation attached to a
lossless frontier is exactly the persistent Smith packet already retained by
that frontier. -/
theorem CanonicalSmithLosslessFrontier.specialFiber_smithReesFamily_eq_packet
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithLosslessFrontier (K := K) D complexity) :
    polynomialFamilySpecialFiber f.smithReesFamily = f.packet := by
  unfold CanonicalSmithLosslessFrontier.smithReesFamily
  unfold CanonicalSmithLosslessFrontier.packet
  exact
    polynomialFamilySpecialFiber_canonicalSmithReesFamily
      (polynomialFamilySpecialFiber f.family)
      f.specialFiber_symmetricDelta_nonnegative

/-- Departure frontiers inherit the canonical Smith-Rees family. -/
noncomputable def CanonicalSmithDepartureFrontier.smithReesFamily
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  f.lossless.smithReesFamily

/-- The Smith-Rees special fibre of a departure frontier is exactly its
retained rank-one packet. -/
theorem CanonicalSmithDepartureFrontier.specialFiber_smithReesFamily_eq_packet
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) :
    polynomialFamilySpecialFiber f.smithReesFamily = f.lossless.packet := by
  exact f.lossless.specialFiber_smithReesFamily_eq_packet

end

end HC4.Valuation
