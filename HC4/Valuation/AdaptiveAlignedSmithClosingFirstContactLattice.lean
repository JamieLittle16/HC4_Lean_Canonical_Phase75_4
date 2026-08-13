import HC4.Valuation.AdaptiveAlignedSmithClosingSeparatedTerminalImpossible
import Mathlib.Tactic

/-!
# First-contact source lattice at an adaptive aligned-Smith closing

The ordinary adaptive Smith exposure deliberately separates every positive
parameter layer from the special fibre.  The preceding green theorem proves
that such a separated exposure cannot realise a terminal direct jump from
positive Hessian defect.

This file introduces the complementary object required at a genuine closing:
a source lattice for which one *positive* parameter layer reaches the divided
level exactly.  Thus for a supported monomial `d` of exact parameter order
`q > 0` we retain

    R * q + weight_W(d) = commonLevel.

No endpoint classification is assumed.  From the lattice data we construct
the actual exposed polynomial family, transport the honest moving gradient
collision, retain the exact transformed Hessian clock, and prove that the
marked longitudinal weight is still forced to be zero.

The positive contact equation is formally incompatible with
`positiveLayerSeparated`; this is the precise Lean-level distinction between
restart exposure and terminal first contact.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Exact Hessian clock for an integral adaptive source exposure, requiring
only positive ramification and nonnegativity of the transformed determinant
exponent.  Unlike `adaptiveSmithExposureFamily_hasHessianDefect`, no
positive-layer separation hypothesis is present. -/
theorem adaptiveSmithFirstContactExposureFamily_hasHessianDefect
    (R : ℕ) (W : Fin 4 → ℕ) (m Delta : ℕ)
    (hR : 0 < R)
    (hnonneg : 4 * m ≤ R * Delta + 2 * ∑ i : Fin 4, W i)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (adaptiveSmithExposureFamily R W m P hint)
      (R * Delta + 2 * ∑ i : Fin 4, W i - 4 * m) := by
  let N := R * Delta + 2 * ∑ i : Fin 4, W i - 4 * m
  have hsum :
      4 * m + N = R * Delta + 2 * ∑ i : Fin 4, W i := by
    dsimp [N]
    omega
  have heq :=
    hessianDeterminant_adaptiveSmithExposureFamily_equation
      R W m hR P hint
  have hram :=
    parameterRamificationFamily_hasHessianDefect
      (K := K) R Delta P hdef
  unfold HasPolynomialFamilyHessianDefect at hram ⊢
  rw [hram] at heq
  simp [adaptiveSmithInflateHom] at heq
  have heq' :
      (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ (4 * m) *
          HC4.Polynomial.hessianDeterminant
            (adaptiveSmithExposureFamily R W m P hint) =
        (MvPolynomial.C Polynomial.X) ^
          (R * Delta + 2 * ∑ i : Fin 4, W i) := by
    simpa only [← pow_mul, ← pow_add, Nat.mul_comm, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using heq
  rw [← hsum, pow_add] at heq'
  have hcancel :
      HC4.Polynomial.hessianDeterminant
          (adaptiveSmithExposureFamily R W m P hint) =
        (MvPolynomial.C Polynomial.X) ^ N :=
    mul_left_cancel₀
      (pow_ne_zero (4 * m)
        (MvPolynomial.C_ne_zero.mpr Polynomial.X_ne_zero)) heq'
  simpa only [map_pow] using hcancel

/-- Integrality alone bounds the divided level by the exact ramified
parameter order plus the source weight.  This is the first-contact analogue
of the separated coefficient-order lemma and does not use layer separation. -/
theorem adaptiveSmithFirstContactExposure_commonLevel_le_exactOrder
    (R : ℕ) (hR : 0 < R)
    {W : Fin 4 → ℕ} {m : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    m ≤ R * smithFamilyCoefficientParameterOrder P d hd +
      Finsupp.weight W d := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  let u := polynomialParameterPrimitivePart c hc
  let v := parameterRamificationHom (K := K) R u
  let total := R * q + Finsupp.weight W d

  have hprimitive : c = Polynomial.X ^ q * u := by
    simpa [q, u, c, smithFamilyCoefficientParameterOrder] using
      (polynomialParameterPrimitivePart_spec c hc)
  have huconst : Polynomial.constantCoeff u ≠ 0 := by
    simpa [u] using
      (polynomialParameterPrimitivePart_constantCoeff_ne_zero c hc)
  have hvconst : Polynomial.constantCoeff v ≠ 0 := by
    change v.coeff 0 ≠ 0
    dsimp [v]
    have hramconst :=
      constantCoeff_parameterRamificationHom (K := K) R hR u
    change
      ((parameterRamificationHom (K := K) R u).coeff 0) =
        u.coeff 0 at hramconst
    change u.coeff 0 ≠ 0 at huconst
    rw [hramconst]
    exact huconst
  have hvne : v ≠ 0 := by
    intro hv
    apply hvconst
    rw [hv]
    simp

  have hfactor :
      adaptiveSmithExposureCoefficientFactor R W P d =
        Polynomial.X ^ total * v := by
    unfold adaptiveSmithExposureCoefficientFactor
    change
      Polynomial.X ^ Finsupp.weight W d *
          parameterRamificationHom (K := K) R c =
        Polynomial.X ^ total * v
    rw [hprimitive, map_mul, parameterRamificationHom_X_pow]
    dsimp [v]
    rw [← mul_assoc, ← pow_add]
    have htotal : Finsupp.weight W d + R * q = total := by
      dsimp [total]
      exact Nat.add_comm _ _
    rw [htotal]

  have hfactorNe :
      adaptiveSmithExposureCoefficientFactor R W P d ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hvne

  have horder :
      polynomialParameterOrder
          (adaptiveSmithExposureCoefficientFactor R W P d) hfactorNe =
        total := by
    exact
      polynomialParameterOrder_eq_of_exact_X_power_factorisation
        (adaptiveSmithExposureCoefficientFactor R W P d)
        hfactorNe total v hvconst hfactor

  have hle :=
    polynomial_X_pow_dvd_le_parameterOrder
      (adaptiveSmithExposureCoefficientFactor R W P d)
      hfactorNe m (hint d hd)
  rw [horder] at hle
  simpa [total] using hle

/-- Exact coefficient factorisation for an arbitrary positive first-contact
exposure. -/
theorem adaptiveSmithFirstContactExposure_supportedCoefficient_exactFactorisation
    (R : ℕ) (hR : 0 < R)
    {W : Fin 4 → ℕ} {m : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hint : HasIntegralAdaptiveSmithExposure R W m P)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    MvPolynomial.coeff d
        (adaptiveSmithExposureFamily R W m P hint) =
      Polynomial.X ^
          (R * smithFamilyCoefficientParameterOrder P d hd +
            Finsupp.weight W d - m) *
        parameterRamificationHom (K := K) R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
  let c := MvPolynomial.coeff d P
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  let u := polynomialParameterPrimitivePart c hc
  let v := parameterRamificationHom (K := K) R u
  let total := R * q + Finsupp.weight W d

  have hprimitive : c = Polynomial.X ^ q * u := by
    simpa [q, u, c, smithFamilyCoefficientParameterOrder] using
      (polynomialParameterPrimitivePart_spec c hc)
  have hfactor :
      adaptiveSmithExposureCoefficientFactor R W P d =
        Polynomial.X ^ total * v := by
    unfold adaptiveSmithExposureCoefficientFactor
    change
      Polynomial.X ^ Finsupp.weight W d *
          parameterRamificationHom (K := K) R c =
        Polynomial.X ^ total * v
    rw [hprimitive, map_mul, parameterRamificationHom_X_pow]
    dsimp [v]
    rw [← mul_assoc, ← pow_add]
    have htotal : Finsupp.weight W d + R * q = total := by
      dsimp [total]
      exact Nat.add_comm _ _
    rw [htotal]

  have hle : m ≤ total := by
    dsimp [total, q]
    exact
      adaptiveSmithFirstContactExposure_commonLevel_le_exactOrder
        R hR P hint hd

  have hid :=
    adaptiveSmithExposureFamily_coefficient_identity R W m P hint d
  have heq :
      Polynomial.X ^ m *
          MvPolynomial.coeff d
            (adaptiveSmithExposureFamily R W m P hint) =
        Polynomial.X ^ m * (Polynomial.X ^ (total - m) * v) := by
    calc
      Polynomial.X ^ m *
          MvPolynomial.coeff d
            (adaptiveSmithExposureFamily R W m P hint) =
          adaptiveSmithExposureCoefficientFactor R W P d := hid
      _ = Polynomial.X ^ total * v := hfactor
      _ = Polynomial.X ^ m * (Polynomial.X ^ (total - m) * v) := by
        rw [← mul_assoc, ← pow_add]
        rw [show m + (total - m) = total by omega]

  have hcancel := polynomial_X_pow_mul_cancel (K := K) m heq
  simpa [total, q, u, v, c] using hcancel

/-- Honest first-contact lattice for the right-recentered blocker source.
The `contactExponent` field records a source monomial on a genuinely positive
parameter layer which lands exactly on the common divided level. -/
structure AdaptiveAlignedSmithClosingFirstContactLatticeData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B) where
  weight : Fin 4 → ℕ
  commonLevel : ℕ
  R : ℕ
  R_pos : 0 < R
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure
      R weight commonLevel
      B.aligned.endpoint.rightRecenteredFamily
  rightSectionIntegrality :
    HasIntegralAdaptiveSmithSection weight
      (parameterRamificationSection
        (K := K) R
        B.aligned.endpoint.rightRecenteredRightSection)
  determinantExponentNonnegative :
    4 * commonLevel ≤
      R * B.aligned.endpoint.defect + 2 * ∑ i : Fin 4, weight i
  contactExponent : Fin 4 →₀ ℕ
  contactSupport :
    contactExponent ∈ B.aligned.endpoint.rightRecenteredFamily.support
  contactOrderPositive :
    0 < smithFamilyCoefficientParameterOrder
      B.aligned.endpoint.rightRecenteredFamily
      contactExponent contactSupport
  contactLevel :
    R * smithFamilyCoefficientParameterOrder
        B.aligned.endpoint.rightRecenteredFamily
        contactExponent contactSupport +
      Finsupp.weight weight contactExponent = commonLevel

namespace AdaptiveAlignedSmithClosingFirstContactLatticeData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- Actual exposed polynomial family at first contact. -/
noncomputable def family
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    L.R L.weight L.commonLevel
    B.aligned.endpoint.rightRecenteredFamily
    L.familyIntegrality

/-- Exact transformed Hessian defect of the first-contact family. -/
def defect
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) : ℕ :=
  L.R * B.aligned.endpoint.defect +
    2 * ∑ i : Fin 4, L.weight i - 4 * L.commonLevel

/-- The first-contact family retains the exact transformed Hessian clock. -/
theorem hessianDefect
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    HasPolynomialFamilyHessianDefect (K := K) L.family L.defect := by
  unfold family defect
  exact
    adaptiveSmithFirstContactExposureFamily_hasHessianDefect
      L.R L.weight L.commonLevel B.aligned.endpoint.defect
      L.R_pos L.determinantExponentNonnegative
      B.aligned.endpoint.rightRecenteredFamily
      L.familyIntegrality source.hessianDefect

/-- Integral pullback of the ramified zero-left section. -/
noncomputable def leftSection
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection
      (K := K) L.R (zeroPolynomialSection (K := K)))
    (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.R L.weight)

/-- Integral pullback of the ramified honest right moving section. -/
noncomputable def rightSection
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection
      (K := K) L.R
      B.aligned.endpoint.rightRecenteredRightSection)
    L.rightSectionIntegrality

/-- The left transported section remains literally zero. -/
theorem leftSection_eq_zero
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    L.leftSection = zeroPolynomialSection (K := K) := by
  funext i
  let aram :=
    parameterRamificationSection
      (K := K) L.R (zeroPolynomialSection (K := K))
  let hdiv : HasIntegralAdaptiveSmithSection L.weight aram :=
    zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.R L.weight
  have hreinflate :=
    congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        L.weight aram hdiv) i
  have hramzero : aram i = 0 := by
    simp [aram, parameterRamificationSection, zeroPolynomialSection]
  have heq :
      Polynomial.X ^ L.weight i *
          integralAdaptiveSmithSection L.weight aram hdiv i =
        Polynomial.X ^ L.weight i * 0 := by
    simpa [adaptiveSmithInflateSection, hramzero] using hreinflate
  have hcancel := polynomial_X_pow_mul_cancel (K := K) (L.weight i) heq
  simpa [leftSection, aram, hdiv, zeroPolynomialSection] using hcancel

/-- Exact moving gradient collision survives first contact. -/
theorem exactCollision
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    HasPolynomialFamilyExactGradientCollision
      L.family L.leftSection L.rightSection := by
  have hram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      L.R
      B.aligned.endpoint.rightRecenteredFamily
      (zeroPolynomialSection (K := K))
      B.aligned.endpoint.rightRecenteredRightSection
      source.exactCollision
  exact
    polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      L.R L.weight L.commonLevel L.R_pos
      B.aligned.endpoint.rightRecenteredFamily
      L.familyIntegrality
      (parameterRamificationSection
        (K := K) L.R (zeroPolynomialSection (K := K)))
      (parameterRamificationSection
        (K := K) L.R
        B.aligned.endpoint.rightRecenteredRightSection)
      (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
        (K := K) L.R L.weight)
      L.rightSectionIntegrality
      hram

/-- Transport of the marked right section still forces longitudinal weight
zero at first contact. -/
theorem weight_zero
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    L.weight (0 : Fin 4) = 0 := by
  let bram :=
    parameterRamificationSection
      (K := K) L.R
      B.aligned.endpoint.rightRecenteredRightSection
  have hconst : Polynomial.constantCoeff (bram (0 : Fin 4)) ≠ 0 := by
    unfold bram parameterRamificationSection
    rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
    exact
      B.aligned.endpoint.rightRecenteredRightSection_constantCoeff_zero_ne
  exact
    integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
      L.weight bram L.rightSectionIntegrality (0 : Fin 4) hconst

/-- The marked right special coordinate is still exactly `-1`. -/
theorem rightSpecial_zero
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    polynomialSectionSpecialPoint L.rightSection (0 : Fin 4) = -1 := by
  let bram :=
    parameterRamificationSection
      (K := K) L.R
      B.aligned.endpoint.rightRecenteredRightSection
  have hreinflate :=
    congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        L.weight bram L.rightSectionIntegrality) (0 : Fin 4)
  have hsection : L.rightSection (0 : Fin 4) = bram (0 : Fin 4) := by
    change
      Polynomial.X ^ L.weight (0 : Fin 4) *
          L.rightSection (0 : Fin 4) = bram (0 : Fin 4) at hreinflate
    rw [L.weight_zero] at hreinflate
    simpa using hreinflate
  unfold polynomialSectionSpecialPoint
  rw [hsection]
  unfold bram parameterRamificationSection
  rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
  have h := congrFun
    B.aligned.endpoint.rightRecenteredRightSection_specialPoint
    (0 : Fin 4)
  change
    Polynomial.constantCoeff
        (B.aligned.endpoint.rightRecenteredRightSection (0 : Fin 4)) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) (0 : Fin 4) at h
  simpa [coordinateAxisPoint] using h

/-- The first-contact special points remain distinct. -/
theorem specialPoints_ne
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    polynomialSectionSpecialPoint L.leftSection ≠
      polynomialSectionSpecialPoint L.rightSection := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  have hleft0 :
      polynomialSectionSpecialPoint L.leftSection (0 : Fin 4) = 0 := by
    rw [L.leftSection_eq_zero]
    simp [polynomialSectionSpecialPoint, zeroPolynomialSection]
  rw [hleft0, L.rightSpecial_zero] at h0
  simp at h0

/-- Specialization of the honest first-contact family carries the distinct
exact collision. -/
theorem specialFiber_exactCollision
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber L.family)
      (polynomialSectionSpecialPoint L.leftSection)
      (polynomialSectionSpecialPoint L.rightSection) := by
  exact
    polynomialFamilyExactGradientCollision_specialFiber
      L.family L.leftSection L.rightSection L.exactCollision

/-- The distinguished positive parameter layer is genuinely visible in
the first-contact special fibre.  Equality at the lattice level leaves
residual order zero, while the primitive coefficient remains nonzero after
positive ramification. -/
theorem contactCoefficient_specialFiber_ne_zero
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    MvPolynomial.coeff L.contactExponent
        (polynomialFamilySpecialFiber L.family) ≠ 0 := by
  let P := B.aligned.endpoint.rightRecenteredFamily
  let d := L.contactExponent
  have hd : d ∈ P.support := by
    simpa [P, d] using L.contactSupport
  have hfac :=
    adaptiveSmithFirstContactExposure_supportedCoefficient_exactFactorisation
      L.R L.R_pos P L.familyIntegrality hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  have hcontact :
      L.R * q + Finsupp.weight L.weight d = L.commonLevel := by
    simpa [P, d, q] using L.contactLevel
  have hres :
      L.R * q + Finsupp.weight L.weight d - L.commonLevel = 0 := by
    rw [hcontact]
    simp
  rw [coeff_polynomialFamilySpecialFiber]
  have hfac' :
      MvPolynomial.coeff d L.family =
        parameterRamificationHom (K := K) L.R
          (polynomialParameterPrimitivePart
            (MvPolynomial.coeff d P)
            (MvPolynomial.mem_support_iff.mp hd)) := by
    simpa [family, P, d, q, hres] using hfac
  rw [hfac']
  rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
  exact
    polynomialParameterPrimitivePart_constantCoeff_ne_zero
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)

/-- The retained positive contact is exactly incompatible with the
`positiveLayerSeparated` condition used by ordinary restart exposures. -/
theorem not_positiveLayerSeparated
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    ¬ (∀ (r : ℕ), 0 < r → ∀ d : Fin 4 →₀ ℕ,
        L.commonLevel < r * L.R + Finsupp.weight L.weight d) := by
  intro hsep
  let q := smithFamilyCoefficientParameterOrder
    B.aligned.endpoint.rightRecenteredFamily
    L.contactExponent L.contactSupport
  have hlt := hsep q (by simpa [q] using L.contactOrderPositive) L.contactExponent
  have heq :
      q * L.R + Finsupp.weight L.weight L.contactExponent =
        L.commonLevel := by
    rw [Nat.mul_comm]
    simpa [q] using L.contactLevel
  rw [heq] at hlt
  exact (Nat.lt_irrefl _ hlt)

end AdaptiveAlignedSmithClosingFirstContactLatticeData

/-! ## Terminal first contact -/

/-- A first-contact lattice whose transformed pure Hessian clock has reached
zero.  This is the correct polynomial-level terminal object for a positive
closing layer; unlike the separated terminal lattice it is not immediately
self-contradictory. -/
structure AdaptiveAlignedSmithClosingFirstContactTerminalData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B) where
  lattice : AdaptiveAlignedSmithClosingFirstContactLatticeData B source
  terminalDefect : lattice.defect = 0

namespace AdaptiveAlignedSmithClosingFirstContactTerminalData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

noncomputable def fibre
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber T.lattice.family

noncomputable def leftPoint
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    Fin 4 → K :=
  polynomialSectionSpecialPoint T.lattice.leftSection

noncomputable def rightPoint
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    Fin 4 → K :=
  polynomialSectionSpecialPoint T.lattice.rightSection

/-- Terminal first contact is an actual polynomial Monge--Ampere fibre. -/
theorem mongeAmpere
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere T.fibre := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere fibre
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := T.lattice.hessianDefect
  rw [T.terminalDefect] at hdef
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  simp

/-- Terminal first contact retains the actual exact collision. -/
theorem exactCollision
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    HasExactGradientCollision T.fibre T.leftPoint T.rightPoint := by
  exact T.lattice.specialFiber_exactCollision

/-- The terminal first-contact points remain distinct. -/
theorem distinct
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    T.leftPoint ≠ T.rightPoint := by
  exact T.lattice.specialPoints_ne

/-- The terminal first-contact lattice still has longitudinal weight zero. -/
theorem weight_zero
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    T.lattice.weight (0 : Fin 4) = 0 :=
  T.lattice.weight_zero

/-- The terminal first-contact right point remains marked by longitudinal
coordinate `-1`. -/
theorem rightPoint_zero
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    T.rightPoint (0 : Fin 4) = -1 :=
  T.lattice.rightSpecial_zero

/-- The terminal first-contact left point is exactly zero. -/
theorem leftPoint_eq_zero
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    T.leftPoint = fun _ : Fin 4 => (0 : K) := by
  unfold leftPoint
  rw [T.lattice.leftSection_eq_zero]
  funext i
  simp [polynomialSectionSpecialPoint, zeroPolynomialSection]

end AdaptiveAlignedSmithClosingFirstContactTerminalData

/-! ## Closing-carrier aliases -/

abbrev AdaptiveAlignedSmithRankOneClosingFirstContactLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingFirstContactLatticeData B C.source

abbrev AdaptiveAlignedSmithZeroSchurClosingFirstContactLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingFirstContactLatticeData B C.source

abbrev AdaptiveAlignedSmithRankOneClosingFirstContactTerminalData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingFirstContactTerminalData B C.source

abbrev AdaptiveAlignedSmithZeroSchurClosingFirstContactTerminalData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingFirstContactTerminalData B C.source

end

end HC4.Valuation
