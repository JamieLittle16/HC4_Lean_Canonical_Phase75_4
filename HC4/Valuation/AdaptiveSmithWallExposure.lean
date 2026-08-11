import HC4.Newton.MixedDegreeFirstWallCompetition
import HC4.Valuation.CanonicalSmithDefectExposure
import Mathlib.Tactic

/-!
# A single ramification scale for an adaptive Smith-wall exposure

This file isolates the finite arithmetic used by the future coefficientwise
Rees construction.  One deliberately oversized ramification index handles
positive parameter layers, transport of every weighted source coordinate,
and nonnegativity of the exposed Hessian-determinant exponent.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Casting a natural source weight into the integers commutes with the
finite weighted degree. -/
theorem weight_natCast_eq
    (W : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i ↦ (W i : ℤ)) d =
      (Finsupp.weight W d : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  push_cast
  rfl

/-- A realised surviving wall has a nonnegative affine source level.  Pole
minimality makes the balanced face nonempty; on any of its realised source
monomials the affine level equals an ordinary natural weighted degree. -/
theorem IntegralAdaptiveSurvivingSmithWall.combinedSourceLevel_nonnegative
    {F : MvPolynomial (Fin 4) K}
    (wall : IntegralAdaptiveSurvivingSmithWall F) :
    0 ≤ wall.realization.combinedSourceLevel wall.level := by
  let S := smithProjectedSupport (1 : Fin 4) 2 3 F
  have hT : (smithSymmetricBalancedSubface S wall.level wall.base).Nonempty :=
    symmetricSmithPoleMinimal_smithSymmetricBalancedSubface_nonempty
      S wall.level wall.base wall.symmetricMinimal wall.minimal
      wall.attained wall.survivingShape
  rcases hT with ⟨e, heT⟩
  have heS : e ∈ S := (mem_smithSymmetricBalancedSubface.mp heT).1
  unfold S smithProjectedSupport at heS
  rcases Finset.mem_image.mp heS with ⟨d, hd, rfl⟩
  have hcombined :
      adaptiveCombinedSmithWeight wall.base wall.level
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) = 0 :=
    (adaptiveCombinedSmithWeight_eq_zero_iff_mem_balancedSubface
      (smithProjectedSupport (1 : Fin 4) 2 3 F)
      wall.base wall.level wall.minimal
      (by
        unfold smithProjectedSupport
        exact Finset.mem_image.mpr ⟨d, hd, rfl⟩)).2 heT
  have hid := combinedSourceWeight_degree_sub_level_eq
    wall.realization wall.level hd
  rw [hcombined] at hid
  have hcast := weight_natCast_eq wall.realization.combinedSourceWeight d
  rw [hcast] at hid
  have hweight : 0 ≤ (Finsupp.weight wall.realization.combinedSourceWeight d : ℤ) := by
    exact_mod_cast (Nat.zero_le (Finsupp.weight wall.realization.combinedSourceWeight d))
  omega

/-- All arithmetic obligations imposed on the one ramification index used
by an adaptive Smith exposure. -/
structure AdaptiveSmithExposureRamificationData
    (W : Fin 4 → ℕ) (m Delta : ℕ) where
  R : ℕ
  R_pos : 0 < R
  /-- Every positive parameter layer remains strictly above the divided
  source-weight level. -/
  positiveLayerSeparated :
    ∀ (r : ℕ), 0 < r → ∀ d : Fin 4 →₀ ℕ,
      m < r * R + Finsupp.weight W d
  /-- The same ramification transports each weighted moving-section
  coordinate integrally. -/
  sectionWeightsCovered : ∀ i : Fin 4, W i ≤ R
  /-- The determinant exponent `RΔ + 2ΣW - 4m` is a natural number. -/
  determinantExponentNonnegative :
    4 * m ≤ R * Delta + 2 * ∑ i : Fin 4, W i

/-- A simple common ramification exists whenever the incoming determinant
clock is positive.  No optimization is needed: `1 + 4m + ΣW` dominates
all three finite requirements. -/
noncomputable def adaptiveSmithExposureRamificationData
    (W : Fin 4 → ℕ) (m Delta : ℕ)
    (hDelta : 0 < Delta) :
    AdaptiveSmithExposureRamificationData W m Delta := by
  let R := 1 + 4 * m + ∑ i : Fin 4, W i
  have hR : 0 < R := by
    dsimp [R]
    omega
  have hmR : m < R := by
    dsimp [R]
    omega
  refine
    { R := R
      R_pos := hR
      positiveLayerSeparated := ?_
      sectionWeightsCovered := ?_
      determinantExponentNonnegative := ?_ }
  · intro r hr d
    have hRle : R ≤ r * R := by
      nlinarith
    have hweight : 0 ≤ Finsupp.weight W d := Nat.zero_le _
    omega
  · intro i
    have hi : W i ≤ ∑ j : Fin 4, W j := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    dsimp [R]
    omega
  · have hDeltaOne : 1 ≤ Delta := hDelta
    have hbase : 4 * m < R := by
      dsimp [R]
      omega
    have hRDelta : R ≤ R * Delta := by
      nlinarith
    omega

/-! ## The integral coefficientwise exposure -/

/-- The unnormalised coefficient obtained by ramifying the parameter and
applying the realised diagonal source weight. -/
def adaptiveSmithExposureCoefficientFactor
    (R : ℕ) (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : Polynomial K :=
  Polynomial.X ^ Finsupp.weight W d *
    parameterRamificationHom (K := K) R (MvPolynomial.coeff d P)

/-- Coefficientwise integrality needed to divide the complete inflated
family by the common level `X^m`. -/
def HasIntegralAdaptiveSmithExposure
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    Polynomial.X ^ m ∣
      adaptiveSmithExposureCoefficientFactor R W P d

/-- The realised surviving wall and one common ramification certificate
imply integrality of every coefficient of the adaptive exposure. -/
theorem IntegralAdaptiveSurvivingSmithWall.hasIntegralAdaptiveSmithExposure
    {Delta : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (wall : IntegralAdaptiveSurvivingSmithWall
      (polynomialFamilySpecialFiber P))
    (m : ℕ)
    (hm : (m : ℤ) = wall.realization.combinedSourceLevel wall.level)
    (ram : AdaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight m Delta) :
    HasIntegralAdaptiveSmithExposure
      ram.R wall.realization.combinedSourceWeight m P := by
  intro d hd
  let q := smithFamilyCoefficientOrder P d
  have hqdiv : Polynomial.X ^ q ∣ MvPolynomial.coeff d P :=
    smithFamilyCoefficientOrder_dvd P hd
  have hramdiv :
      Polynomial.X ^ (ram.R * q) ∣
        parameterRamificationHom (K := K) ram.R
          (MvPolynomial.coeff d P) :=
    parameterRamification_pow_dvd ram.R q _ hqdiv
  have hle :
      m ≤ ram.R * q +
        Finsupp.weight wall.realization.combinedSourceWeight d := by
    by_cases hq0 : q = 0
    · have hspecial :
          d ∈ (polynomialFamilySpecialFiber P).support :=
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber P hd).1 hq0
      have hnonneg := adaptiveCombinedSmithWeight_nonnegative
        (smithProjectedSupport (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        wall.base wall.level wall.minimal wall.survivingShape
        (by
          unfold smithProjectedSupport
          exact Finset.mem_image.mpr ⟨d, hspecial, rfl⟩)
      have hid := combinedSourceWeight_degree_sub_level_eq
        wall.realization wall.level hspecial
      have hcast := weight_natCast_eq
        wall.realization.combinedSourceWeight d
      rw [hcast, ← hm] at hid
      rw [hq0]
      norm_num
      omega
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have := ram.positiveLayerSeparated q hqpos d
      simpa [Nat.mul_comm] using Nat.le_of_lt this
  rcases hramdiv with ⟨a, ha⟩
  refine ⟨Polynomial.X ^
      (ram.R * q + Finsupp.weight wall.realization.combinedSourceWeight d - m) * a, ?_⟩
  unfold adaptiveSmithExposureCoefficientFactor
  rw [ha]
  have hexp :
      m + (ram.R * q +
          Finsupp.weight wall.realization.combinedSourceWeight d - m) =
        Finsupp.weight wall.realization.combinedSourceWeight d + ram.R * q := by
    omega
  calc
    Polynomial.X ^ Finsupp.weight wall.realization.combinedSourceWeight d *
          (Polynomial.X ^ (ram.R * q) * a) =
        Polynomial.X ^
            (Finsupp.weight wall.realization.combinedSourceWeight d + ram.R * q) * a := by
          rw [← mul_assoc, ← pow_add]
    _ = Polynomial.X ^ m *
          (Polynomial.X ^
            (ram.R * q + Finsupp.weight wall.realization.combinedSourceWeight d - m) * a) := by
          rw [← mul_assoc, ← pow_add, hexp]

/-- A chosen integral quotient of one inflated coefficient. -/
noncomputable def adaptiveSmithExposureCoefficientQuotient
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (d : Fin 4 →₀ ℕ) : Polynomial K :=
  if hd : d ∈ P.support then Classical.choose (hint d hd) else 0

theorem adaptiveSmithExposureCoefficientQuotient_spec_of_mem
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    Polynomial.X ^ m *
        adaptiveSmithExposureCoefficientQuotient R W m P hint d =
      adaptiveSmithExposureCoefficientFactor R W P d := by
  unfold adaptiveSmithExposureCoefficientQuotient
  rw [dif_pos hd]
  exact (Classical.choose_spec (hint d hd)).symm

/-- Honest integral adaptive Smith-wall exposure. -/
noncomputable def adaptiveSmithExposureFamily
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (adaptiveSmithExposureCoefficientQuotient R W m P hint d)

theorem coeff_adaptiveSmithExposureFamily
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (adaptiveSmithExposureFamily R W m P hint) =
      adaptiveSmithExposureCoefficientQuotient R W m P hint d := by
  classical
  by_cases hd : d ∈ P.support
  · unfold adaptiveSmithExposureFamily
    simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd]
  · unfold adaptiveSmithExposureFamily
    simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd,
      adaptiveSmithExposureCoefficientQuotient]

/-- Exact coefficient identity replacing the informal Laurent formula.
Every later covariance argument should be derived from this polynomial
identity. -/
theorem adaptiveSmithExposureFamily_coefficient_identity
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ m *
        MvPolynomial.coeff d (adaptiveSmithExposureFamily R W m P hint) =
      adaptiveSmithExposureCoefficientFactor R W P d := by
  rw [coeff_adaptiveSmithExposureFamily]
  by_cases hd : d ∈ P.support
  · exact adaptiveSmithExposureCoefficientQuotient_spec_of_mem
      R W m P hint hd
  · have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [adaptiveSmithExposureCoefficientQuotient,
      adaptiveSmithExposureCoefficientFactor, hd, hcoeff]

/-- Residual parameter order of a supported source coefficient after the
adaptive normalization. -/
def adaptiveSmithExposureResidualExponent
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) : ℕ :=
  R * smithFamilyCoefficientOrder P d + Finsupp.weight W d - m

/-- A residual exponent is zero precisely for an order-zero coefficient on
the selected balanced Smith subface. -/
theorem IntegralAdaptiveSurvivingSmithWall.residualExponent_eq_zero_iff
    {Delta : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (wall : IntegralAdaptiveSurvivingSmithWall
      (polynomialFamilySpecialFiber P))
    (m : ℕ)
    (hm : (m : ℤ) = wall.realization.combinedSourceLevel wall.level)
    (ram : AdaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight m Delta)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    adaptiveSmithExposureResidualExponent ram.R
        wall.realization.combinedSourceWeight m P d = 0 ↔
      smithFamilyCoefficientOrder P d = 0 ∧
        smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
          smithSymmetricBalancedSubface
            (smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber P))
            wall.level wall.base := by
  let q := smithFamilyCoefficientOrder P d
  let e := smithSupportExponentOf (1 : Fin 4) 2 3 d
  constructor
  · intro hzero
    have hq0 : q = 0 := by
      by_contra hq
      have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      have hsep := ram.positiveLayerSeparated q hqpos d
      unfold adaptiveSmithExposureResidualExponent at hzero
      dsimp [q] at hzero hsep
      have hsep' :
          m < ram.R * smithFamilyCoefficientOrder P d +
            Finsupp.weight wall.realization.combinedSourceWeight d := by
        simpa [Nat.mul_comm] using hsep
      omega
    change smithFamilyCoefficientOrder P d = 0 at hq0
    have hspecial : d ∈ (polynomialFamilySpecialFiber P).support :=
      (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber P hd).1 hq0
    have heSupport : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P) := by
      unfold e smithProjectedSupport
      exact Finset.mem_image.mpr ⟨d, hspecial, rfl⟩
    have hid := combinedSourceWeight_degree_sub_level_eq
      wall.realization wall.level hspecial
    have hcast := weight_natCast_eq wall.realization.combinedSourceWeight d
    have hnonneg : 0 ≤ adaptiveCombinedSmithWeight wall.base wall.level e :=
      adaptiveCombinedSmithWeight_nonnegative
        (smithProjectedSupport (1 : Fin 4) 2 3
          (polynomialFamilySpecialFiber P))
        wall.base wall.level wall.minimal wall.survivingShape heSupport
    have hcombined : adaptiveCombinedSmithWeight wall.base wall.level e = 0 := by
      unfold adaptiveSmithExposureResidualExponent at hzero
      dsimp [e] at hzero hnonneg ⊢
      rw [hq0] at hzero
      norm_num at hzero
      rw [hcast, ← hm] at hid
      omega
    exact ⟨hq0,
      (adaptiveCombinedSmithWeight_eq_zero_iff_mem_balancedSubface
        _ wall.base wall.level wall.minimal heSupport).1 hcombined⟩
  · rintro ⟨hq0, heT⟩
    have hspecial : d ∈ (polynomialFamilySpecialFiber P).support :=
      (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber P hd).1 hq0
    have heSupport : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber P) := by
      unfold e smithProjectedSupport
      exact Finset.mem_image.mpr ⟨d, hspecial, rfl⟩
    have hcombined : adaptiveCombinedSmithWeight wall.base wall.level e = 0 :=
      (adaptiveCombinedSmithWeight_eq_zero_iff_mem_balancedSubface
        _ wall.base wall.level wall.minimal heSupport).2 heT
    have hid := combinedSourceWeight_degree_sub_level_eq
      wall.realization wall.level hspecial
    have hcast := weight_natCast_eq wall.realization.combinedSourceWeight d
    rw [hcast, ← hm, hcombined] at hid
    change smithFamilyCoefficientOrder P d = 0 at hq0
    unfold adaptiveSmithExposureResidualExponent
    rw [hq0]
    norm_num
    omega

/-- Constant coefficient of an exposed supported coefficient.  It is the
old special-fibre coefficient exactly on the selected residual-zero face,
and vanishes otherwise. -/
theorem IntegralAdaptiveSurvivingSmithWall.constantCoeff_exposureCoefficient
    {Delta : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (wall : IntegralAdaptiveSurvivingSmithWall
      (polynomialFamilySpecialFiber P))
    (m : ℕ)
    (hm : (m : ℤ) = wall.realization.combinedSourceLevel wall.level)
    (ram : AdaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight m Delta)
    (hint : HasIntegralAdaptiveSmithExposure ram.R
      wall.realization.combinedSourceWeight m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    Polynomial.constantCoeff
        (MvPolynomial.coeff d
          (adaptiveSmithExposureFamily ram.R
            wall.realization.combinedSourceWeight m P hint)) =
      if adaptiveSmithExposureResidualExponent ram.R
          wall.realization.combinedSourceWeight m P d = 0 then
        Polynomial.constantCoeff (MvPolynomial.coeff d P)
      else 0 := by
  let q := smithFamilyCoefficientOrder P d
  let w := Finsupp.weight wall.realization.combinedSourceWeight d
  let res := adaptiveSmithExposureResidualExponent ram.R
    wall.realization.combinedSourceWeight m P d
  have hidentity := adaptiveSmithExposureFamily_coefficient_identity
    ram.R wall.realization.combinedSourceWeight m P hint d
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff m) hidentity
  dsimp only at hcoeff
  rw [Polynomial.coeff_X_pow_mul'] at hcoeff
  simp only [le_refl, if_true, Nat.sub_self] at hcoeff
  by_cases hres : res = 0
  · have hclocks :=
      (IntegralAdaptiveSurvivingSmithWall.residualExponent_eq_zero_iff
        P wall m hm ram hd).1 hres
    have hq0 : q = 0 := hclocks.1
    have hw : w = m := by
      have hspecial :=
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber P hd).1 hq0
      have hsupport : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
          smithProjectedSupport (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber P) := by
        unfold smithProjectedSupport
        exact Finset.mem_image.mpr ⟨d, hspecial, rfl⟩
      have hcombined :=
        (adaptiveCombinedSmithWeight_eq_zero_iff_mem_balancedSubface
          _ wall.base wall.level wall.minimal hsupport).2 hclocks.2
      have hid := combinedSourceWeight_degree_sub_level_eq
        wall.realization wall.level hspecial
      have hcast := weight_natCast_eq wall.realization.combinedSourceWeight d
      rw [hcast, ← hm, hcombined] at hid
      dsimp [w]
      omega
    have hres' : adaptiveSmithExposureResidualExponent ram.R
        wall.realization.combinedSourceWeight m P d = 0 := by
      simpa [res] using hres
    rw [if_pos hres']
    unfold adaptiveSmithExposureCoefficientFactor at hcoeff
    dsimp [w] at hw
    rw [hw, Polynomial.coeff_X_pow_mul'] at hcoeff
    simp only [le_refl, if_true, Nat.sub_self] at hcoeff
    have hramconst := constantCoeff_parameterRamificationHom
      ram.R ram.R_pos (MvPolynomial.coeff d P)
    change
      ((parameterRamificationHom (K := K) ram.R
          (MvPolynomial.coeff d P)).coeff 0) =
        (MvPolynomial.coeff d P).coeff 0 at hramconst
    exact hcoeff.trans hramconst
  · have hrespos : 0 < res := Nat.pos_of_ne_zero hres
    have hres' : adaptiveSmithExposureResidualExponent ram.R
        wall.realization.combinedSourceWeight m P d ≠ 0 := by
      simpa [res] using hres
    have hqdiv : Polynomial.X ^ q ∣ MvPolynomial.coeff d P :=
      smithFamilyCoefficientOrder_dvd P hd
    have hramdiv : Polynomial.X ^ (ram.R * q) ∣
        parameterRamificationHom (K := K) ram.R
          (MvPolynomial.coeff d P) :=
      parameterRamification_pow_dvd ram.R q _ hqdiv
    rcases hramdiv with ⟨a, ha⟩
    have htotal : m < w + ram.R * q := by
      unfold res adaptiveSmithExposureResidualExponent at hrespos
      dsimp [q, w] at hrespos ⊢
      omega
    rw [if_neg hres']
    unfold adaptiveSmithExposureCoefficientFactor at hcoeff
    rw [ha] at hcoeff
    have hfactor :
        Polynomial.X ^ Finsupp.weight wall.realization.combinedSourceWeight d *
            (Polynomial.X ^ (ram.R * q) * a) =
          Polynomial.X ^ (w + ram.R * q) * a := by
      dsimp [w]
      rw [← mul_assoc, ← pow_add]
    rw [hfactor, Polynomial.coeff_X_pow_mul'] at hcoeff
    simp [Nat.not_le.mpr htotal] at hcoeff
    exact hcoeff

/-- **Exact adaptive Smith special fibre.**  The honest integral exposure
selects precisely the symmetric balanced subface of the incoming special
fibre; no positive parameter layer survives. -/
theorem IntegralAdaptiveSurvivingSmithWall.specialFiber_adaptiveSmithExposureFamily
    {Delta : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (wall : IntegralAdaptiveSurvivingSmithWall
      (polynomialFamilySpecialFiber P))
    (m : ℕ)
    (hm : (m : ℤ) = wall.realization.combinedSourceLevel wall.level)
    (ram : AdaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight m Delta)
    (hint : HasIntegralAdaptiveSmithExposure ram.R
      wall.realization.combinedSourceWeight m P) :
    polynomialFamilySpecialFiber
        (adaptiveSmithExposureFamily ram.R
          wall.realization.combinedSourceWeight m P hint) =
      smithSubfacePolynomial (1 : Fin 4) 2 3
        (smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3
            (polynomialFamilySpecialFiber P))
          wall.level wall.base)
        (polynomialFamilySpecialFiber P) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_polynomialFamilySpecialFiber,
    coeff_smithSubfacePolynomial,
    coeff_polynomialFamilySpecialFiber]
  by_cases hd : d ∈ P.support
  · rw [IntegralAdaptiveSurvivingSmithWall.constantCoeff_exposureCoefficient
      P wall m hm ram hint hd]
    let res := adaptiveSmithExposureResidualExponent ram.R
      wall.realization.combinedSourceWeight m P d
    by_cases hres : res = 0
    · have hclocks :=
        (IntegralAdaptiveSurvivingSmithWall.residualExponent_eq_zero_iff
          P wall m hm ram hd).1 hres
      have hres' : adaptiveSmithExposureResidualExponent ram.R
          wall.realization.combinedSourceWeight m P d = 0 := by
        simpa [res] using hres
      rw [if_pos hres', if_pos hclocks.2]
    · have hres' : adaptiveSmithExposureResidualExponent ram.R
          wall.realization.combinedSourceWeight m P d ≠ 0 := by
        simpa [res] using hres
      rw [if_neg hres']
      by_cases heT : smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
          smithSymmetricBalancedSubface
            (smithProjectedSupport (1 : Fin 4) 2 3
              (polynomialFamilySpecialFiber P))
            wall.level wall.base
      · rw [if_pos heT]
        have horder : smithFamilyCoefficientOrder P d ≠ 0 := by
          intro hzero
          exact hres'
            ((IntegralAdaptiveSurvivingSmithWall.residualExponent_eq_zero_iff
              P wall m hm ram hd).2 ⟨hzero, heT⟩)
        have hnotSpecial :
            d ∉ (polynomialFamilySpecialFiber P).support := by
          intro hspecial
          exact horder
            ((smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
              P hd).2 hspecial)
        have hz := MvPolynomial.notMem_support_iff.mp hnotSpecial
        rw [coeff_polynomialFamilySpecialFiber] at hz
        exact hz.symm
      · rw [if_neg heT]
  · have hcoeff : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [coeff_adaptiveSmithExposureFamily]
    simp [adaptiveSmithExposureCoefficientQuotient, hd, hcoeff]

/-! ## Whole-polynomial normalization identity -/

/-- Diagonal source inflation attached to an arbitrary natural weight. -/
def adaptiveSmithInflateSection
    (W : Fin 4 → ℕ) (a : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  fun i => Polynomial.X ^ W i * a i

/-- Source variable under the adaptive diagonal inflation. -/
def adaptiveSmithInflateVariable
    (W : Fin 4 → ℕ) (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.C (Polynomial.X ^ W i) * MvPolynomial.X i

/-- Honest polynomial-ring source substitution by the adaptive diagonal. -/
noncomputable def adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom MvPolynomial.C (adaptiveSmithInflateVariable W)

theorem eval_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval a (adaptiveSmithInflateHom W P) =
      MvPolynomial.eval (adaptiveSmithInflateSection W a) P := by
  change MvPolynomial.eval a
      (MvPolynomial.eval₂ MvPolynomial.C
        (adaptiveSmithInflateVariable W) P) = _
  rw [← MvPolynomial.eval_assoc (adaptiveSmithInflateVariable W) a P]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext i
  simp [adaptiveSmithInflateVariable, adaptiveSmithInflateSection]

/-- Product identity for a source monomial under the adaptive diagonal. -/
theorem fin4_adaptiveSmithInflateSection_monomialProduct
    (W : Fin 4 → ℕ) (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ) :
    (∏ i : Fin 4, adaptiveSmithInflateSection W a i ^ d i) =
      Polynomial.X ^ Finsupp.weight W d * ∏ i : Fin 4, a i ^ d i := by
  unfold adaptiveSmithInflateSection
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.prod_univ_four, Fin.prod_univ_four, Fin.sum_univ_four]
    simp only [mul_pow, ← pow_mul]
    calc
      (Polynomial.X ^ (W 0 * d 0) * a 0 ^ d 0) *
          (Polynomial.X ^ (W 1 * d 1) * a 1 ^ d 1) *
          (Polynomial.X ^ (W 2 * d 2) * a 2 ^ d 2) *
          (Polynomial.X ^ (W 3 * d 3) * a 3 ^ d 3) =
        (Polynomial.X ^ (W 0 * d 0) *
          Polynomial.X ^ (W 1 * d 1) *
          Polynomial.X ^ (W 2 * d 2) *
          Polynomial.X ^ (W 3 * d 3)) *
          (a 0 ^ d 0 * a 1 ^ d 1 * a 2 ^ d 2 * a 3 ^ d 3) := by ring
      _ = Polynomial.X ^
          (W 0 * d 0 + (W 1 * d 1 + (W 2 * d 2 + W 3 * d 3))) *
          (a 0 ^ d 0 * a 1 ^ d 1 * a 2 ^ d 2 * a 3 ^ d 3) := by
        repeat' rw [← pow_add]
        simp [Nat.add_assoc]
      _ = Polynomial.X ^
          (d 0 * W 0 + (d 1 * W 1 + (d 2 * W 2 + d 3 * W 3))) *
          (a 0 ^ d 0 * a 1 ^ d 1 * a 2 ^ d 2 * a 3 ^ d 3) := by
        simp [Nat.mul_comm]
    simp [nsmul_eq_mul, Nat.add_assoc]
  · intro i
    simp

/-- Evaluation form of the normalized adaptive identity. -/
theorem eval_adaptiveSmithExposureFamily
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (a : Fin 4 → Polynomial K) :
    Polynomial.X ^ m *
        MvPolynomial.eval a (adaptiveSmithExposureFamily R W m P hint) =
      MvPolynomial.eval (adaptiveSmithInflateSection W a)
        (parameterRamificationFamily (K := K) R P) := by
  classical
  unfold adaptiveSmithExposureFamily
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  rw [Finset.mul_sum]
  rw [MvPolynomial.eval_eq']
  have hsupport :
      (parameterRamificationFamily (K := K) R P).support = P.support := by
    apply Finset.Subset.antisymm
    · exact MvPolynomial.support_map_subset
        (parameterRamificationHom (K := K) R) P
    · intro d hd
      apply MvPolynomial.mem_support_iff.mpr
      unfold parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      exact parameterRamificationHom_ne_zero_of_pos R hR
        (MvPolynomial.mem_support_iff.mp hd)
  rw [hsupport]
  apply Finset.sum_congr rfl
  intro d hd
  rw [fin4_adaptiveSmithInflateSection_monomialProduct]
  rw [Finsupp.prod_fintype d (fun n e => a n ^ e) (by simp)]
  calc
    Polynomial.X ^ m *
        (adaptiveSmithExposureCoefficientQuotient R W m P hint d *
          ∏ i : Fin 4, a i ^ d i) =
      (Polynomial.X ^ m *
        adaptiveSmithExposureCoefficientQuotient R W m P hint d) *
          ∏ i : Fin 4, a i ^ d i := by ring
    _ = adaptiveSmithExposureCoefficientFactor R W P d *
          ∏ i : Fin 4, a i ^ d i := by
      rw [adaptiveSmithExposureCoefficientQuotient_spec_of_mem
        R W m P hint hd]
    _ = MvPolynomial.coeff d (parameterRamificationFamily (K := K) R P) *
          (Polynomial.X ^ Finsupp.weight W d *
            ∏ i : Fin 4, a i ^ d i) := by
      unfold adaptiveSmithExposureCoefficientFactor parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      ring

/-- **Exact normalized whole-polynomial identity.** -/
theorem adaptiveSmithInflate_adaptiveSmithExposureFamily_eq
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ)
    (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P) :
    adaptiveSmithInflateHom W
        (parameterRamificationFamily (K := K) R P) =
      MvPolynomial.C (Polynomial.X ^ m) *
        adaptiveSmithExposureFamily R W m P hint := by
  apply MvPolynomial.funext
  intro a
  rw [eval_adaptiveSmithInflateHom]
  simp only [map_mul, MvPolynomial.eval_C]
  exact (eval_adaptiveSmithExposureFamily R W m hR P hint a).symm

/-! ## Gradient covariance and collision transport -/

/-- First-order chain rule for the adaptive diagonal inflation. -/
theorem pderiv_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) (i : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv i (adaptiveSmithInflateHom W P) =
      MvPolynomial.C (Polynomial.X ^ W i) *
        adaptiveSmithInflateHom W (MvPolynomial.pderiv i P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [adaptiveSmithInflateHom]
  · intro p q hp hq
    simp [hp, hq, mul_add]
  · intro p n hp
    have hp' :
        MvPolynomial.pderiv i
            (MvPolynomial.bind₁ (adaptiveSmithInflateVariable W) p) =
          MvPolynomial.C (Polynomial.X ^ W i) *
            MvPolynomial.bind₁ (adaptiveSmithInflateVariable W)
              (MvPolynomial.pderiv i p) := by
      simpa [adaptiveSmithInflateHom] using hp
    by_cases hni : n = i
    · subst n
      simp [adaptiveSmithInflateHom, adaptiveSmithInflateVariable, hp']
      ring
    · have hin : i ≠ n := Ne.symm hni
      simp [adaptiveSmithInflateHom, adaptiveSmithInflateVariable,
        hp', hni, hin]
      ring

/-- Integrality condition for pulling a polynomial section back through
the adaptive source diagonal. -/
def HasIntegralAdaptiveSmithSection
    (W : Fin 4 → ℕ) (a : Fin 4 → Polynomial K) : Prop :=
  ∀ i : Fin 4, Polynomial.X ^ W i ∣ a i

/-- Chosen integral pullback of a section through the source diagonal. -/
noncomputable def integralAdaptiveSmithSection
    (W : Fin 4 → ℕ) (a : Fin 4 → Polynomial K)
    (hdiv : HasIntegralAdaptiveSmithSection W a) :
    Fin 4 → Polynomial K :=
  fun i => Classical.choose (hdiv i)

theorem adaptiveSmithInflateSection_integralSection_eq
    (W : Fin 4 → ℕ) (a : Fin 4 → Polynomial K)
    (hdiv : HasIntegralAdaptiveSmithSection W a) :
    adaptiveSmithInflateSection W
        (integralAdaptiveSmithSection W a hdiv) = a := by
  funext i
  unfold adaptiveSmithInflateSection integralAdaptiveSmithSection
  exact (Classical.choose_spec (hdiv i)).symm

/-- Derivative evaluation covariance for the normalized adaptive family. -/
theorem eval_pderiv_adaptiveSmithExposureFamily
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ) (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (a : Fin 4 → Polynomial K)
    (hadiv : HasIntegralAdaptiveSmithSection W a)
    (i : Fin 4) :
    Polynomial.X ^ m *
        MvPolynomial.eval (integralAdaptiveSmithSection W a hadiv)
          (MvPolynomial.pderiv i
            (adaptiveSmithExposureFamily R W m P hint)) =
      Polynomial.X ^ W i *
        MvPolynomial.eval a
          (MvPolynomial.pderiv i
            (parameterRamificationFamily (K := K) R P)) := by
  let a' := integralAdaptiveSmithSection W a hadiv
  have hpoly := adaptiveSmithInflate_adaptiveSmithExposureFamily_eq
    R W m hR P hint
  have hpd := congrArg (MvPolynomial.pderiv i) hpoly
  rw [pderiv_adaptiveSmithInflateHom] at hpd
  rw [MvPolynomial.pderiv_C_mul] at hpd
  have heval := congrArg (MvPolynomial.eval a') hpd
  have hsection : adaptiveSmithInflateSection W a' = a :=
    adaptiveSmithInflateSection_integralSection_eq W a hadiv
  dsimp [a'] at heval ⊢
  simp only [map_mul, MvPolynomial.eval_C] at heval
  rw [eval_adaptiveSmithInflateHom, hsection] at heval
  exact heval.symm

/-- Exact gradient collision survives the integral adaptive exposure once
both ramified sections are divisible by the source weights. -/
theorem polynomialFamilyExactGradientCollision_adaptiveSmithExposure
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ) (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (a b : Fin 4 → Polynomial K)
    (hadiv : HasIntegralAdaptiveSmithSection W a)
    (hbdiv : HasIntegralAdaptiveSmithSection W b)
    (hcoll : HasPolynomialFamilyExactGradientCollision
      (parameterRamificationFamily (K := K) R P) a b) :
    HasPolynomialFamilyExactGradientCollision
      (adaptiveSmithExposureFamily R W m P hint)
      (integralAdaptiveSmithSection W a hadiv)
      (integralAdaptiveSmithSection W b hbdiv) := by
  intro i
  apply polynomial_X_pow_mul_cancel (K := K) m
  calc
    Polynomial.X ^ m *
        MvPolynomial.eval (integralAdaptiveSmithSection W a hadiv)
          (MvPolynomial.pderiv i
            (adaptiveSmithExposureFamily R W m P hint)) =
      Polynomial.X ^ W i *
        MvPolynomial.eval a
          (MvPolynomial.pderiv i
            (parameterRamificationFamily (K := K) R P)) :=
      eval_pderiv_adaptiveSmithExposureFamily
        R W m hR P hint a hadiv i
    _ = Polynomial.X ^ W i *
        MvPolynomial.eval b
          (MvPolynomial.pderiv i
            (parameterRamificationFamily (K := K) R P)) := by
      rw [hcoll i]
    _ = Polynomial.X ^ m *
        MvPolynomial.eval (integralAdaptiveSmithSection W b hbdiv)
          (MvPolynomial.pderiv i
            (adaptiveSmithExposureFamily R W m P hint)) :=
      (eval_pderiv_adaptiveSmithExposureFamily
        R W m hR P hint b hbdiv i).symm

/-- Ramification makes a section integrally divisible by every covered
source weight, provided each positively weighted coordinate vanishes at the
special parameter. -/
theorem parameterRamificationSection_hasIntegralAdaptiveSmithSection
    (R : ℕ) (W : Fin 4 → ℕ) (hcover : ∀ i, W i ≤ R)
    (a : Fin 4 → Polynomial K)
    (hspecial : ∀ i, W i = 0 ∨ Polynomial.constantCoeff (a i) = 0) :
    HasIntegralAdaptiveSmithSection W
      (parameterRamificationSection (K := K) R a) := by
  intro i
  rcases hspecial i with hi | hi
  · rw [hi]
    simp
  · have hXdvd : Polynomial.X ∣ a i := Polynomial.X_dvd_iff.mpr hi
    have hXdvd' : Polynomial.X ^ 1 ∣ a i := by simpa using hXdvd
    have hram : Polynomial.X ^ R ∣
        parameterRamificationHom (K := K) R (a i) := by
      simpa using parameterRamification_pow_dvd R 1 (a i) hXdvd'
    exact dvd_trans
      (polynomial_X_pow_dvd_X_pow_of_le (K := K) (W i) R (hcover i))
      hram

/-- Collision transport from the original family through ramification and
the adaptive integral source exposure. -/
theorem polynomialFamilyExactGradientCollision_ramifiedAdaptiveSmithExposure
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ) (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (a b : Fin 4 → Polynomial K)
    (hcover : ∀ i, W i ≤ R)
    (haSpecial : ∀ i, W i = 0 ∨ Polynomial.constantCoeff (a i) = 0)
    (hbSpecial : ∀ i, W i = 0 ∨ Polynomial.constantCoeff (b i) = 0)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    HasPolynomialFamilyExactGradientCollision
      (adaptiveSmithExposureFamily R W m P hint)
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) R a)
        (parameterRamificationSection_hasIntegralAdaptiveSmithSection
          R W hcover a haSpecial))
      (integralAdaptiveSmithSection W
        (parameterRamificationSection (K := K) R b)
        (parameterRamificationSection_hasIntegralAdaptiveSmithSection
          R W hcover b hbSpecial)) := by
  exact polynomialFamilyExactGradientCollision_adaptiveSmithExposure
    R W m hR P hint
    (parameterRamificationSection (K := K) R a)
    (parameterRamificationSection (K := K) R b)
    (parameterRamificationSection_hasIntegralAdaptiveSmithSection
      R W hcover a haSpecial)
    (parameterRamificationSection_hasIntegralAdaptiveSmithSection
      R W hcover b hbSpecial)
    (polynomialFamilyExactGradientCollision_parameterRamification
      R P a b hcoll)

/-! ## Hessian covariance -/

theorem hessian_adaptiveSmithInflateHom_entry
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian (adaptiveSmithInflateHom W P) i j =
      MvPolynomial.C (Polynomial.X ^ W i) *
        MvPolynomial.C (Polynomial.X ^ W j) *
          adaptiveSmithInflateHom W (HC4.Polynomial.hessian P i j) := by
  rw [HC4.Polynomial.hessian_apply]
  rw [pderiv_adaptiveSmithInflateHom W i P]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_adaptiveSmithInflateHom W j (MvPolynomial.pderiv i P)]
  rw [HC4.Polynomial.hessian_apply]
  ring

theorem prod_adaptiveSmithDerivativeCoefficient
    (W : Fin 4 → ℕ) :
    (∏ i : Fin 4,
      (MvPolynomial.C (Polynomial.X ^ W i) :
        MvPolynomial (Fin 4) (Polynomial K))) =
      MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i) := by
  rw [Fin.prod_univ_four, Fin.sum_univ_four]
  simp only [← map_mul, ← pow_add]

/-- Hessian determinant under an arbitrary integral diagonal source
inflation. -/
theorem hessianDeterminant_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant (adaptiveSmithInflateHom W P) =
      (MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i)) ^ 2 *
        adaptiveSmithInflateHom W
          (HC4.Polynomial.hessianDeterminant P) := by
  let v : Fin 4 → MvPolynomial (Fin 4) (Polynomial K) :=
    fun i => MvPolynomial.C (Polynomial.X ^ W i)
  let A : Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
    (adaptiveSmithInflateHom W).mapMatrix (HC4.Polynomial.hessian P)
  have hmatrix :
      HC4.Polynomial.hessian (adaptiveSmithInflateHom W P) =
        fun i j => v i * (v j * A i j) := by
    apply Matrix.ext
    intro i j
    simpa [v, A, mul_assoc] using
      hessian_adaptiveSmithInflateHom_entry W P i j
  have hv : (∏ i : Fin 4, v i) =
      MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i) := by
    simpa [v] using prod_adaptiveSmithDerivativeCoefficient (K := K) W
  have hrow :
      (Matrix.det fun i j => v j * A i j) =
        (∏ i : Fin 4, v i) * A.det := Matrix.det_mul_row v A
  have hmapdet : A.det = adaptiveSmithInflateHom W
      ((HC4.Polynomial.hessian P).det) := by
    simpa [A] using
      (RingHom.map_det (adaptiveSmithInflateHom W)
        (HC4.Polynomial.hessian P)).symm
  unfold HC4.Polynomial.hessianDeterminant
  rw [hmatrix]
  calc
    (Matrix.det fun i j => v i * (v j * A i j)) =
        (∏ i : Fin 4, v i) *
          (Matrix.det fun i j => v j * A i j) :=
      Matrix.det_mul_column v (fun i j => v j * A i j)
    _ = (∏ i : Fin 4, v i) * ((∏ i : Fin 4, v i) * A.det) := by
      rw [hrow]
    _ = (MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i)) ^ 2 *
          A.det := by rw [hv]; ring
    _ = (MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i)) ^ 2 *
          adaptiveSmithInflateHom W ((HC4.Polynomial.hessian P).det) := by
      rw [hmapdet]

/-- Determinant covariance equation for the normalized adaptive exposure.
This is the integral equation from which the exact exposed clock is
obtained by monomial cancellation. -/
theorem hessianDeterminant_adaptiveSmithExposureFamily_equation
    (R : ℕ) (W : Fin 4 → ℕ) (m : ℕ) (hR : 0 < R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P) :
    (MvPolynomial.C (Polynomial.X ^ m) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 4 *
        HC4.Polynomial.hessianDeterminant
          (adaptiveSmithExposureFamily R W m P hint) =
      (MvPolynomial.C (Polynomial.X ^ ∑ i : Fin 4, W i)) ^ 2 *
        adaptiveSmithInflateHom W
          (HC4.Polynomial.hessianDeterminant
            (parameterRamificationFamily (K := K) R P)) := by
  have hpoly := adaptiveSmithInflate_adaptiveSmithExposureFamily_eq
    R W m hR P hint
  have hdet := congrArg HC4.Polynomial.hessianDeterminant hpoly
  rw [hessianDeterminant_adaptiveSmithInflateHom] at hdet
  rw [hessianDeterminant_C_mul] at hdet
  exact hdet.symm

/-- The adaptive exposure carries an exact pure Hessian clock.  The
ramification certificate guarantees that the exponent left after removing
the four common normalization factors is a natural number. -/
theorem adaptiveSmithExposureFamily_hasHessianDefect
    (R : ℕ) (W : Fin 4 → ℕ) (m Delta : ℕ)
    (ram : AdaptiveSmithExposureRamificationData W m Delta)
    (hR : R = ram.R)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (adaptiveSmithExposureFamily R W m P hint)
      (R * Delta + 2 * ∑ i : Fin 4, W i - 4 * m) := by
  subst R
  let N := ram.R * Delta + 2 * ∑ i : Fin 4, W i - 4 * m
  have hsum : 4 * m + N =
      ram.R * Delta + 2 * ∑ i : Fin 4, W i := by
    have hle := ram.determinantExponentNonnegative
    dsimp [N]
    omega
  have heq := hessianDeterminant_adaptiveSmithExposureFamily_equation
    ram.R W m ram.R_pos P hint
  have hram := parameterRamificationFamily_hasHessianDefect
    (K := K) ram.R Delta P hdef
  unfold HasPolynomialFamilyHessianDefect at hram ⊢
  rw [hram] at heq
  simp [adaptiveSmithInflateHom] at heq
  have heq' :
      (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ (4 * m) *
          HC4.Polynomial.hessianDeterminant
            (adaptiveSmithExposureFamily ram.R W m P hint) =
        (MvPolynomial.C Polynomial.X) ^
          (ram.R * Delta + 2 * ∑ i : Fin 4, W i) := by
    simpa only [← pow_mul, ← pow_add, Nat.mul_comm, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using heq
  rw [← hsum, pow_add] at heq'
  have hcancel : HC4.Polynomial.hessianDeterminant
        (adaptiveSmithExposureFamily ram.R W m P hint) =
      (MvPolynomial.C Polynomial.X) ^ N :=
    mul_left_cancel₀
      (pow_ne_zero (4 * m) (MvPolynomial.C_ne_zero.mpr Polynomial.X_ne_zero)) heq'
  simpa only [map_pow] using hcancel
end

end HC4.Valuation
