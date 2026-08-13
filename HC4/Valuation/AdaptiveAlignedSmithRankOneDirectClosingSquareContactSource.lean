import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingTransverseAlignment
import HC4.Valuation.AdaptiveAlignedSmithFirstContactSquareContactElimination
import Mathlib.Tactic

/-!
# Coordinate-free direct-closing square source for first contact

The direct-closing equality branch now yields either a fresh longitudinal
square on the original right-recentered source, or a fresh transverse square
after a marked-axis-preserving determinant-one source equivalence.

The older first-contact carrier is hard-coded to the original blocker source,
so it cannot consume the transverse aligned family directly.  This file
removes that artificial mismatch.  It packages both cases as one marked
square source and gives that source its own generic first-contact lattice.

No supporting lattice is manufactured here: existence of that finite lattice
is the remaining Newton-polyhedral selection problem.  Once supplied, all
polynomial geometry (Hessian clock, moving collision, marked point and
terminal Monge--Ampere fibre) is recovered without JC2.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A single source-level carrier covering both direct-closing square cases.
The family may be the original right-recentered family or its honest
marked-axis-preserving three-transvection copy. -/
structure DirectClosingAlignedSquareSourceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  family : MvPolynomial (Fin 4) (Polynomial K)
  rightSection : Fin 4 → Polynomial K
  index : Fin 4
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      family B.aligned.endpoint.defect
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (zeroPolynomialSection (K := K)) rightSection
  rightSpecialPoint :
    polynomialSectionSpecialPoint rightSection =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  squareSupport :
    directClosingQuadraticExponent index index ∈ family.support
  squareOrder :
    smithFamilyCoefficientParameterOrder
      family (directClosingQuadraticExponent index index) squareSupport =
        C.firstActualLayerOrder
  squareOrderPositive : 0 < C.firstActualLayerOrder
  squareCoeff_zero :
    (MvPolynomial.coeff (directClosingQuadraticExponent index index)
      family).coeff 0 = 0
  squareCoeff_first_ne :
    (MvPolynomial.coeff (directClosingQuadraticExponent index index)
      family).coeff C.firstActualLayerOrder ≠ 0

namespace DirectClosingAlignedSquareSourceData

/-- The distinguished fresh square exponent. -/
def squareExponent
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) : Fin 4 →₀ ℕ :=
  directClosingQuadraticExponent D.index D.index

/-- The square has genuinely positive exact parameter order. -/
theorem exactOrder_pos
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) :
    0 < smithFamilyCoefficientParameterOrder D.family
      D.squareExponent (by simpa [squareExponent] using D.squareSupport) := by
  let hd : D.squareExponent ∈ D.family.support := by
    simpa [squareExponent] using D.squareSupport
  have horder :
      smithFamilyCoefficientParameterOrder D.family D.squareExponent hd =
        C.firstActualLayerOrder := by
    simpa [squareExponent] using D.squareOrder
  rw [horder]
  exact D.squareOrderPositive

/-- The marked longitudinal coordinate of the transported right section still
has nonzero special value. -/
theorem rightSection_constantCoeff_zero_ne
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) :
    Polynomial.constantCoeff (D.rightSection (0 : Fin 4)) ≠ 0 := by
  have h := congrFun D.rightSpecialPoint (0 : Fin 4)
  change
    Polynomial.constantCoeff (D.rightSection (0 : Fin 4)) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) (0 : Fin 4) at h
  rw [h]
  simp [coordinateAxisPoint]

end DirectClosingAlignedSquareSourceData

/-- The original longitudinal fresh-square branch is already a marked square
source without changing coordinates. -/
noncomputable def directClosingLongitudinalSquareSource
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (h : C.HasFreshDirectClosingSquareAt (0 : Fin 4)) :
    DirectClosingAlignedSquareSourceData C := by
  let d := directClosingQuadraticExponent (0 : Fin 4) (0 : Fin 4)
  have hsupp : d ∈ C.family.support := by
    exact C.mem_family_support_of_coeff_at_ne_zero h.2.1
  have hparam :
      smithFamilyCoefficientParameterOrder C.family d hsupp =
        C.firstActualLayerOrder := by
    rw [← smithFamilyCoefficientOrder_eq C.family hsupp]
    exact h.2.2
  exact {
    family := C.family
    rightSection := B.aligned.endpoint.rightRecenteredRightSection
    index := 0
    hessianDefect := C.family_hessianDefect
    exactCollision := C.family_exactCollision
    rightSpecialPoint :=
      B.aligned.endpoint.rightRecenteredRightSection_specialPoint
    squareSupport := by simpa [d] using hsupp
    squareOrder := by simpa [d] using hparam
    squareOrderPositive := C.firstActualLayerOrder_pos
    squareCoeff_zero := h.1
    squareCoeff_first_ne := h.2.1
  }

/-- A transverse aligned-square package is the same marked square source with
the source-equivalent family and inverse-transformed right section. -/
noncomputable def DirectClosingTransverseAlignedSquareData.toAlignedSquareSource
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingTransverseAlignedSquareData C) :
    DirectClosingAlignedSquareSourceData C := by
  let Q := D.family
  let d := directClosingQuadraticExponent D.ell D.ell
  have hsupp : d ∈ Q.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply D.squareCoeff_first_ne
    have hzj :=
      congrArg (fun p : Polynomial K => p.coeff C.firstActualLayerOrder) hz
    simpa [Q, d, DirectClosingTransverseAlignedSquareData.family] using hzj
  have hparam : smithFamilyCoefficientParameterOrder Q d hsupp =
      C.firstActualLayerOrder := by
    rw [← smithFamilyCoefficientOrder_eq Q hsupp]
    simpa [DirectClosingTransverseAlignedSquareData.family, Q, d] using D.squareOrder
  exact {
    family := Q
    rightSection := D.rightSection
    index := D.ell
    hessianDefect := by
      simpa [DirectClosingTransverseAlignedSquareData.family, Q] using D.hessianDefect
    exactCollision := by
      simpa [DirectClosingTransverseAlignedSquareData.family,
        DirectClosingTransverseAlignedSquareData.rightSection, Q] using D.exactCollision
    rightSpecialPoint := by
      simpa [DirectClosingTransverseAlignedSquareData.rightSection] using D.rightSpecialPoint
    squareSupport := by simpa [d] using hsupp
    squareOrder := by simpa [d] using hparam
    squareOrderPositive := C.firstActualLayerOrder_pos
    squareCoeff_zero := by
      simpa [DirectClosingTransverseAlignedSquareData.family, Q, d] using D.squareCoeff_zero
    squareCoeff_first_ne := by
      simpa [DirectClosingTransverseAlignedSquareData.family, Q, d] using D.squareCoeff_first_ne
  }

/-- **Unified direct-closing fresh-square source.**
At `j = Delta` there is always an honest marked polynomial source carrying a
square of exact positive parameter order `j`, with the exact determinant
clock and moving collision retained. -/
theorem directClosing_exists_alignedSquareSource
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    Nonempty (DirectClosingAlignedSquareSourceData C) := by
  rcases C.directClosing_freshLongitudinalSquare_or_transverseAlignedSquare heq with
    hlong | htrans
  · exact ⟨C.directClosingLongitudinalSquareSource hlong⟩
  · rcases htrans with ⟨D⟩
    exact ⟨D.toAlignedSquareSource⟩

/-! ## Generic first-contact lattice on the aligned square source -/

/-- Finite first-contact data on the actual aligned square source.
Unlike the older blocker-specific structure, this is parameterised by the
source-equivalent family itself, so the transverse branch is a first-class
input rather than an out-of-band coordinate change. -/
structure DirectClosingSquareFirstContactLatticeData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C) where
  weight : Fin 4 → ℕ
  commonLevel : ℕ
  R : ℕ
  R_pos : 0 < R
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure R weight commonLevel D.family
  rightSectionIntegrality :
    HasIntegralAdaptiveSmithSection weight
      (parameterRamificationSection (K := K) R D.rightSection)
  determinantExponentNonnegative :
    4 * commonLevel ≤
      R * B.aligned.endpoint.defect + 2 * ∑ i : Fin 4, weight i
  squareContactLevel :
    R * C.firstActualLayerOrder +
      Finsupp.weight weight D.squareExponent = commonLevel

namespace DirectClosingSquareFirstContactLatticeData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {D : DirectClosingAlignedSquareSourceData C}

/-- The actual exposed family at square first contact. -/
noncomputable def family
    (L : DirectClosingSquareFirstContactLatticeData D) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    L.R L.weight L.commonLevel D.family L.familyIntegrality

/-- Exact transformed Hessian defect. -/
def defect (L : DirectClosingSquareFirstContactLatticeData D) : ℕ :=
  L.R * B.aligned.endpoint.defect +
    2 * ∑ i : Fin 4, L.weight i - 4 * L.commonLevel

/-- The square contact is an honest exact-order positive contact, not merely
an actual-layer coefficient. -/
theorem squareContactLevel_exactOrder
    (L : DirectClosingSquareFirstContactLatticeData D) :
    L.R * smithFamilyCoefficientParameterOrder
        D.family D.squareExponent
        (by simpa [DirectClosingAlignedSquareSourceData.squareExponent] using D.squareSupport) +
      Finsupp.weight L.weight D.squareExponent = L.commonLevel := by
  let hd : D.squareExponent ∈ D.family.support := by
    simpa [DirectClosingAlignedSquareSourceData.squareExponent] using D.squareSupport
  have horder :
      smithFamilyCoefficientParameterOrder D.family D.squareExponent hd =
        C.firstActualLayerOrder := by
    simpa [DirectClosingAlignedSquareSourceData.squareExponent] using D.squareOrder
  simpa [horder] using L.squareContactLevel

/-- The first-contact family retains the exact transformed Hessian clock. -/
theorem hessianDefect
    (L : DirectClosingSquareFirstContactLatticeData D) :
    HasPolynomialFamilyHessianDefect (K := K) L.family L.defect := by
  unfold family defect
  exact adaptiveSmithFirstContactExposureFamily_hasHessianDefect
    L.R L.weight L.commonLevel B.aligned.endpoint.defect
    L.R_pos L.determinantExponentNonnegative
    D.family L.familyIntegrality D.hessianDefect

/-- Integral pullback of the ramified zero-left section. -/
noncomputable def leftSection
    (L : DirectClosingSquareFirstContactLatticeData D) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection
      (K := K) L.R (zeroPolynomialSection (K := K)))
    (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.R L.weight)

/-- Integral pullback of the ramified marked right section. -/
noncomputable def rightSection
    (L : DirectClosingSquareFirstContactLatticeData D) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection (K := K) L.R D.rightSection)
    L.rightSectionIntegrality

/-- The pulled-back left section is literally zero. -/
theorem leftSection_eq_zero
    (L : DirectClosingSquareFirstContactLatticeData D) :
    L.leftSection = zeroPolynomialSection (K := K) := by
  funext i
  let aram := parameterRamificationSection
    (K := K) L.R (zeroPolynomialSection (K := K))
  let hdiv : HasIntegralAdaptiveSmithSection L.weight aram :=
    zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.R L.weight
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq L.weight aram hdiv) i
  have hramzero : aram i = 0 := by
    simp [aram, parameterRamificationSection, zeroPolynomialSection]
  have heq :
      Polynomial.X ^ L.weight i *
          integralAdaptiveSmithSection L.weight aram hdiv i =
        Polynomial.X ^ L.weight i * 0 := by
    simpa [adaptiveSmithInflateSection, hramzero] using hreinflate
  have hcancel := polynomial_X_pow_mul_cancel (K := K) (L.weight i) heq
  simpa [leftSection, aram, hdiv, zeroPolynomialSection] using hcancel

/-- Exact moving gradient collision survives square first contact. -/
theorem exactCollision
    (L : DirectClosingSquareFirstContactLatticeData D) :
    HasPolynomialFamilyExactGradientCollision
      L.family L.leftSection L.rightSection := by
  have hram := polynomialFamilyExactGradientCollision_parameterRamification
    L.R D.family (zeroPolynomialSection (K := K)) D.rightSection D.exactCollision
  exact polynomialFamilyExactGradientCollision_adaptiveSmithExposure
    L.R L.weight L.commonLevel L.R_pos
    D.family L.familyIntegrality
    (parameterRamificationSection
      (K := K) L.R (zeroPolynomialSection (K := K)))
    (parameterRamificationSection (K := K) L.R D.rightSection)
    (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.R L.weight)
    L.rightSectionIntegrality hram

/-- Marked-point integrality forces longitudinal exposure weight zero. -/
theorem weight_zero
    (L : DirectClosingSquareFirstContactLatticeData D) :
    L.weight (0 : Fin 4) = 0 := by
  let bram := parameterRamificationSection (K := K) L.R D.rightSection
  have hconst : Polynomial.constantCoeff (bram (0 : Fin 4)) ≠ 0 := by
    unfold bram parameterRamificationSection
    rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
    exact D.rightSection_constantCoeff_zero_ne
  exact integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
    L.weight bram L.rightSectionIntegrality (0 : Fin 4) hconst

/-- The right special longitudinal coordinate remains exactly `-1`. -/
theorem rightSpecial_zero
    (L : DirectClosingSquareFirstContactLatticeData D) :
    polynomialSectionSpecialPoint L.rightSection (0 : Fin 4) = -1 := by
  let bram := parameterRamificationSection (K := K) L.R D.rightSection
  have hreinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq
      L.weight bram L.rightSectionIntegrality) (0 : Fin 4)
  have hsection : L.rightSection (0 : Fin 4) = bram (0 : Fin 4) := by
    change Polynomial.X ^ L.weight (0 : Fin 4) *
        L.rightSection (0 : Fin 4) = bram (0 : Fin 4) at hreinflate
    rw [L.weight_zero] at hreinflate
    simpa using hreinflate
  unfold polynomialSectionSpecialPoint
  rw [hsection]
  unfold bram parameterRamificationSection
  rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
  have h := congrFun D.rightSpecialPoint (0 : Fin 4)
  change Polynomial.constantCoeff (D.rightSection (0 : Fin 4)) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) (0 : Fin 4) at h
  simpa [coordinateAxisPoint] using h

/-- The first-contact special points remain distinct. -/
theorem specialPoints_ne
    (L : DirectClosingSquareFirstContactLatticeData D) :
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

/-- The distinguished fresh square survives on the first-contact special fibre. -/
theorem squareCoefficient_specialFiber_ne_zero
    (L : DirectClosingSquareFirstContactLatticeData D) :
    MvPolynomial.coeff D.squareExponent
        (polynomialFamilySpecialFiber L.family) ≠ 0 := by
  let P := D.family
  let d := D.squareExponent
  have hd : d ∈ P.support := by
    simpa [P, d, DirectClosingAlignedSquareSourceData.squareExponent] using D.squareSupport
  have hfac :=
    adaptiveSmithFirstContactExposure_supportedCoefficient_exactFactorisation
      L.R L.R_pos P L.familyIntegrality hd
  let q := smithFamilyCoefficientParameterOrder P d hd
  have hcontact :
      L.R * q + Finsupp.weight L.weight d = L.commonLevel := by
    simpa [P, d, q] using L.squareContactLevel_exactOrder
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
  change Polynomial.constantCoeff (MvPolynomial.coeff d L.family) ≠ 0
  rw [hfac']
  rw [constantCoeff_parameterRamificationHom L.R L.R_pos]
  exact polynomialParameterPrimitivePart_constantCoeff_ne_zero
    (MvPolynomial.coeff d P)
    (MvPolynomial.mem_support_iff.mp hd)

/-- Specialization carries the distinct exact collision. -/
theorem specialFiber_exactCollision
    (L : DirectClosingSquareFirstContactLatticeData D) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber L.family)
      (polynomialSectionSpecialPoint L.leftSection)
      (polynomialSectionSpecialPoint L.rightSection) := by
  exact polynomialFamilyExactGradientCollision_specialFiber
    L.family L.leftSection L.rightSection L.exactCollision

end DirectClosingSquareFirstContactLatticeData

/-- Terminal square first contact for the generic aligned source. -/
structure DirectClosingSquareFirstContactTerminalData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    (L : DirectClosingSquareFirstContactLatticeData D) where
  terminalDefect : L.defect = 0

namespace DirectClosingSquareFirstContactTerminalData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {D : DirectClosingAlignedSquareSourceData C}
variable {L : DirectClosingSquareFirstContactLatticeData D}

noncomputable def fibre
    (T : DirectClosingSquareFirstContactTerminalData L) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber L.family

noncomputable def leftPoint
    (T : DirectClosingSquareFirstContactTerminalData L) : Fin 4 → K :=
  polynomialSectionSpecialPoint L.leftSection

noncomputable def rightPoint
    (T : DirectClosingSquareFirstContactTerminalData L) : Fin 4 → K :=
  polynomialSectionSpecialPoint L.rightSection

/-- Terminal square first contact is an actual polynomial Monge--Ampere fibre. -/
theorem mongeAmpere
    (T : DirectClosingSquareFirstContactTerminalData L) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere T.fibre := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere fibre
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := L.hessianDefect
  rw [T.terminalDefect] at hdef
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  simp

/-- The exact collision survives specialization at terminal square contact. -/
theorem exactCollision
    (T : DirectClosingSquareFirstContactTerminalData L) :
    HasExactGradientCollision T.fibre T.leftPoint T.rightPoint := by
  exact polynomialFamilyExactGradientCollision_specialFiber
    L.family L.leftSection L.rightSection L.exactCollision

/-- The terminal collision points remain distinct. -/
theorem distinct
    (T : DirectClosingSquareFirstContactTerminalData L) :
    T.leftPoint ≠ T.rightPoint := by
  exact L.specialPoints_ne

/-- The terminal left point is literally zero. -/
theorem leftPoint_eq_zero
    (T : DirectClosingSquareFirstContactTerminalData L) :
    T.leftPoint = fun _ : Fin 4 => (0 : K) := by
  unfold leftPoint
  rw [L.leftSection_eq_zero]
  funext i
  simp [polynomialSectionSpecialPoint, zeroPolynomialSection]

/-- The terminal right point keeps longitudinal coordinate `-1`. -/
theorem rightPoint_zero
    (T : DirectClosingSquareFirstContactTerminalData L) :
    T.rightPoint (0 : Fin 4) = -1 := by
  exact L.rightSpecial_zero

/-- The fresh square survives in the terminal fibre. -/
theorem squareCoefficient_ne_zero
    (T : DirectClosingSquareFirstContactTerminalData L) :
    MvPolynomial.coeff D.squareExponent T.fibre ≠ 0 := by
  simpa [fibre] using L.squareCoefficient_specialFiber_ne_zero

/-- The terminal Monge--Ampere fibre has nondegenerate actual Hessian at the origin. -/
theorem mongeAmpere_hasNondegenerateActualHessian
    (T : DirectClosingSquareFirstContactTerminalData L) :
    HasNondegenerateTerminalActualHessian (0 : Fin 4) 1 2 3 T.fibre := by
  unfold HasNondegenerateTerminalActualHessian
  have hmatrix :
      terminalActualHessianMatrix (0 : Fin 4) 1 2 3 T.fibre =
        quadraticFamilyHessianMatrix T.fibre := by
    ext i j
    unfold terminalActualHessianMatrix quadraticFamilyHessianMatrix
    simp only [terminalFourCoordinate_standard]
    unfold mvHessianComponentAt
    change
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j T.fibre)) =
        MvPolynomial.constantCoeff
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i T.fibre))
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
    rw [pderiv_comm_commRing i j T.fibre]
  rw [hmatrix, quadraticFamilyHessianMatrix_det]
  have hMA := T.mongeAmpere
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere at hMA
  rw [hMA]
  simp

end DirectClosingSquareFirstContactTerminalData

/-- Constant section attached to the generic terminal right point. -/
noncomputable def directClosingSquareTerminalRightConstantSection
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L) :
    Fin 4 → Polynomial K :=
  polynomialConstantSection T.rightPoint

/-- Honest terminal cocharacter on a generic aligned-square first-contact fibre. -/
structure DirectClosingSquareFirstContactTerminalCocharacterData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {D : DirectClosingAlignedSquareSourceData C}
    {L : DirectClosingSquareFirstContactLatticeData D}
    (T : DirectClosingSquareFirstContactTerminalData L) where
  weight : Fin 4 → ℕ
  degree : ℕ
  nontrivial : IsNontrivialIntegralWeight (fun i => (weight i : ℤ))
  homogeneous :
    IsIntegralWeightedHomogeneous
      (fun i => (weight i : ℤ)) (degree : ℤ) T.fibre
  rightPointIntegrality :
    HasIntegralAdaptiveSmithSection
      weight (directClosingSquareTerminalRightConstantSection T)

namespace DirectClosingSquareFirstContactTerminalCocharacterData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {D : DirectClosingAlignedSquareSourceData C}
variable {L : DirectClosingSquareFirstContactLatticeData D}
variable {T : DirectClosingSquareFirstContactTerminalData L}

/-- The terminal cocharacter is nonnegative. -/
theorem nonnegative
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    IsNonnegativeIntegralWeight (fun i => (E.weight i : ℤ)) := by
  intro i
  show (0 : ℤ) ≤ (E.weight i : ℤ)
  exact Int.ofNat_nonneg _

/-- Honest transport of the marked right point forces longitudinal weight zero. -/
theorem weight_zero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    E.weight (0 : Fin 4) = 0 := by
  apply integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
    E.weight (directClosingSquareTerminalRightConstantSection T)
    E.rightPointIntegrality (0 : Fin 4)
  unfold directClosingSquareTerminalRightConstantSection polynomialConstantSection
  simpa using (show T.rightPoint (0 : Fin 4) ≠ 0 by rw [T.rightPoint_zero]; simp)

/-- Integral form of the marked zero. -/
theorem integralWeight_zero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    (fun i => (E.weight i : ℤ)) (0 : Fin 4) = 0 := by
  simp [E.weight_zero]

/-- The terminal collision rules out the scalar branch. -/
theorem residualNonScalarJump
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    HasResidualNonScalarTerminalJump
      (fun i => (E.weight i : ℤ)) (E.degree : ℤ) T.fibre := by
  exact terminalDirectRankJump_collision_forces_residual
    E.nontrivial E.homogeneous T.mongeAmpere_hasNondegenerateActualHessian
    T.leftPoint T.rightPoint T.distinct T.exactCollision

/-- Every nonzero coordinate of the right point has zero terminal weight. -/
theorem weight_eq_zero_of_rightPoint_ne_zero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (i : Fin 4) (hi : T.rightPoint i ≠ 0) :
    E.weight i = 0 := by
  apply integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
    E.weight (directClosingSquareTerminalRightConstantSection T)
    E.rightPointIntegrality i
  unfold directClosingSquareTerminalRightConstantSection polynomialConstantSection
  simpa using hi

/-- A second marked zero is a zero terminal weight away from coordinate zero. -/
def HasSecondMarkedTerminalZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) : Prop :=
  ∃ i : Fin 4, i ≠ 0 ∧ E.weight i = 0

/-- Without a second zero, the right point is exactly `-e0`. -/
theorem rightPoint_eq_negativeLongitudinalAxis_of_noSecondZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (hno : ¬ E.HasSecondMarkedTerminalZero) :
    T.rightPoint = negativeLongitudinalAxisPoint (K := K) := by
  funext i
  by_cases hi : i = 0
  · subst i
    simpa [negativeLongitudinalAxisPoint, coordinateAxisPoint] using T.rightPoint_zero
  · have hweight : E.weight i ≠ 0 := by
      intro hz
      exact hno ⟨i, hi, hz⟩
    have hp : T.rightPoint i = 0 := by
      by_contra hpne
      exact hweight (E.weight_eq_zero_of_rightPoint_ne_zero i hpne)
    simp [negativeLongitudinalAxisPoint, coordinateAxisPoint, hi, hp]

/-- No-second-zero gives the canonical marked-axis collision. -/
theorem exactMarkedAxisCollision_of_noSecondZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (hno : ¬ E.HasSecondMarkedTerminalZero) :
    HasExactGradientCollision T.fibre
      (fun _ : Fin 4 => (0 : K))
      (negativeLongitudinalAxisPoint (K := K)) := by
  have hcoll := T.exactCollision
  rw [T.leftPoint_eq_zero, E.rightPoint_eq_negativeLongitudinalAxis_of_noSecondZero hno] at hcoll
  exact hcoll

/-- Unique-zero terminal geometry is impossible without JC2. -/
theorem impossible_of_noSecondMarkedZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (hno : ¬ E.HasSecondMarkedTerminalZero) : False := by
  let lambda : Fin 4 → ℤ := fun i => (E.weight i : ℤ)
  let d : ℤ := (E.degree : ℤ)
  have hunique : ∀ i : Fin 4, lambda i = 0 → i = 0 := by
    intro i hi
    by_contra hine
    apply hno
    refine ⟨i, hine, ?_⟩
    dsimp [lambda] at hi
    exact_mod_cast hi
  rcases uniqueZeroTerminalWeight_standardizes
      E.residualNonScalarJump.1 E.nonnegative E.integralWeight_zero hunique with
    ⟨rho, a, hfix, ha, had, hweight⟩
  have hweightFun :
      (fun i : Fin 4 => lambda (rho.symm i)) =
        standardOneZeroTerminalWeight d a := by
    funext i
    exact hweight i
  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight d a) d
        (MvPolynomial.rename rho T.fibre) := by
    have h := integralWeightedHomogeneous_rename_perm E.homogeneous rho
    dsimp [lambda, d] at hweightFun ⊢
    rw [hweightFun] at h
    exact h
  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere (MvPolynomial.rename rho T.fibre) :=
    isPolynomialMongeAmpere_rename_perm rho T.mongeAmpere
  have hcoll := (E.exactMarkedAxisCollision_of_noSecondZero hno).rename_perm rho
  have hcollMarked :
      HasExactGradientCollision (MvPolynomial.rename rho T.fibre)
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K)) := by
    rw [terminalPermutePoint_zeroPoint] at hcoll
    rw [terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero rho hfix] at hcoll
    exact hcoll
  exact standardOneZero_negativeLongitudinalAxis_collision_impossible
    ha had hhomRenamed hMARenamed hcollMarked

/-- Every surviving terminal cocharacter has a second zero. -/
theorem hasSecondMarkedTerminalZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    E.HasSecondMarkedTerminalZero := by
  by_contra hno
  exact E.impossible_of_noSecondMarkedZero hno

/-- The terminal degree is positive. -/
theorem degree_pos
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    0 < (E.degree : ℤ) := by
  exact nonnegative_nonScalar_terminal_degree_pos
    E.residualNonScalarJump.1 E.nonnegative

/-- Every terminal weight is bounded by the terminal degree. -/
theorem weight_le_degree
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (i : Fin 4) :
    (E.weight i : ℤ) ≤ (E.degree : ℤ) := by
  exact nonnegative_terminal_weight_le_degree
    E.residualNonScalarJump.1 E.nonnegative i

/-- The square contact has terminal weighted degree exactly `degree`. -/
theorem squareContact_weightedDegree
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    integralWeightedDegree (fun i => (E.weight i : ℤ)) D.squareExponent =
      (E.degree : ℤ) := by
  exact E.homogeneous D.squareExponent T.squareCoefficient_ne_zero

/-- For the distinguished square, `2*w_i = degree`. -/
theorem squareContact_weightSum
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    (E.weight D.index : ℤ) + (E.weight D.index : ℤ) = (E.degree : ℤ) := by
  have hcoeff :
      MvPolynomial.coeff (HC4.Newton.quadraticExponent D.index D.index) T.fibre ≠ 0 := by
    simpa [DirectClosingAlignedSquareSourceData.squareExponent,
      AdaptiveAlignedSmithRankOneClosingSourceCarrier.directClosingQuadraticExponent,
      HC4.Newton.quadraticExponent, add_comm] using T.squareCoefficient_ne_zero
  exact weightedHomogeneous_quadraticCoeff_weightSum
    E.homogeneous D.index D.index hcoeff

/-- The square coordinate has positive terminal weight. -/
theorem squareContact_weight_pos
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    0 < E.weight D.index := by
  have hsum := E.squareContact_weightSum
  have hdpos : 0 < (E.degree : ℤ) := E.degree_pos
  have hiInt : 0 < (E.weight D.index : ℤ) := by linarith
  exact_mod_cast hiInt

/-- The complement matching forces total terminal weight `2*degree`. -/
theorem totalWeight_eq_two_degree
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) :
    (∑ i : Fin 4, (E.weight i : ℤ)) = 2 * (E.degree : ℤ) := by
  rcases nonScalarTerminalConformalFace_has_complementWeightPermutation
      E.residualNonScalarJump.1 with ⟨pi, hpi⟩
  have hsum :
      (∑ i : Fin 4, ((E.weight (pi i) : ℤ) + (E.weight i : ℤ))) =
        ∑ _i : Fin 4, (E.degree : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpi i
  have hperm :
      (∑ i : Fin 4, (E.weight (pi i) : ℤ)) =
        ∑ i : Fin 4, (E.weight i : ℤ) := by
    simpa using (Equiv.sum_comp pi (fun i : Fin 4 => (E.weight i : ℤ)))
  rw [Finset.sum_add_distrib, hperm] at hsum
  have hbalance :
      2 * (∑ i : Fin 4, (E.weight i : ℤ)) = 4 * (E.degree : ℤ) := by
    simpa [two_mul, Fin.sum_univ_four] using hsum
  linarith

/-- Outside two distinct zero coordinates every terminal weight is full degree. -/
theorem weight_eq_degree_of_secondZero
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T)
    (z i : Fin 4) (hz0 : z ≠ 0) (hzw : E.weight z = 0)
    (hi0 : i ≠ 0) (hiz : i ≠ z) :
    E.weight i = E.degree := by
  have htotal := E.totalWeight_eq_two_degree
  have htotal4 :
      (E.weight 0 : ℤ) + (E.weight 1 : ℤ) +
          (E.weight 2 : ℤ) + (E.weight 3 : ℤ) =
        2 * (E.degree : ℤ) := by
    simpa [Fin.sum_univ_four] using htotal
  have h0 : E.weight (0 : Fin 4) = 0 := E.weight_zero
  have hle0 := E.weight_le_degree (0 : Fin 4)
  have hle1 := E.weight_le_degree (1 : Fin 4)
  have hle2 := E.weight_le_degree (2 : Fin 4)
  have hle3 := E.weight_le_degree (3 : Fin 4)
  fin_cases z <;> fin_cases i <;> simp_all <;> omega

/-- **Generic aligned-square terminal contradiction, without JC2.** -/
theorem impossible
    (E : DirectClosingSquareFirstContactTerminalCocharacterData T) : False := by
  have hiPos : 0 < E.weight D.index := E.squareContact_weight_pos
  have hi0 : D.index ≠ 0 := by
    intro hi
    rw [hi, E.weight_zero] at hiPos
    omega
  rcases E.hasSecondMarkedTerminalZero with ⟨z, hz0, hzw⟩
  have hzi : z ≠ D.index := by
    intro hzi
    subst z
    rw [hzw] at hiPos
    omega
  have hiDegree : E.weight D.index = E.degree :=
    E.weight_eq_degree_of_secondZero z D.index hz0 hzw hi0 (Ne.symm hzi)
  have hsum := E.squareContact_weightSum
  have hdpos : 0 < (E.degree : ℤ) := E.degree_pos
  rw [hiDegree] at hsum
  linarith

end DirectClosingSquareFirstContactTerminalCocharacterData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
