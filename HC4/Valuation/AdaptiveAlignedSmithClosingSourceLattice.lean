import HC4.Valuation.AdaptiveAlignedSmithCanonicalChartDispatcher
import HC4.Valuation.AdaptiveAlignedSmithMarkedAxisTerminal
import HC4.Valuation.AdaptiveRigidMatrixExposure
import Mathlib.Tactic

/-!
# Honest source-lattice exposure at an adaptive aligned-Smith closing

The chart-lossless canonical dispatcher now retains the actual right-recentered
polynomial family, its exact moving collision, its pure Hessian clock, and the
precise coordinate/swap/shear Hessian chart which closes.

The remaining terminal adapter should not be allowed to manufacture an
associated-graded polynomial from a matrix clock.  This file removes most of
that adapter by constructing the polynomial-level source-lattice exposure
once the finite divisibility data of the lattice is supplied.

For one blocker closing source and a natural source weight `W`, common level
`m`, and the standard one-shot ramification certificate, we retain only two
integrality inputs:

* coefficientwise integrality of the whole recentered family after source
  inflation and common-level division;
* integral pullback of the ramified right moving section.

Everything geometric is then a theorem:

* the exposed family is an actual polynomial family;
* the exact Hessian determinant clock is the expected
  `R*Delta + 2*sum(W) - 4*m`;
* the exact moving gradient collision survives;
* the left pulled-back section is literally zero;
* the marked longitudinal source weight is forced to be zero, rather than
  assumed;
* the right special point still has longitudinal coordinate `-1`, hence the
  two special points remain distinct.

If the transformed defect is zero, specialization produces an honest
four-variable polynomial Monge--Ampere fibre with a distinct exact gradient
collision.  Thus the later terminal theorem only has to certify the weighted
endpoint type of this *already constructed* polynomial fibre.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The ramified zero section is integrally divisible by every natural source
weight. -/
theorem zeroRamifiedSection_hasIntegralAdaptiveSmithSection
    (R : ℕ) (W : Fin 4 → ℕ) :
    HasIntegralAdaptiveSmithSection W
      (parameterRamificationSection
        (K := K) R (zeroPolynomialSection (K := K))) := by
  intro i
  simp [parameterRamificationSection, zeroPolynomialSection]

/-- Finite lattice/divisibility data needed to expose the *actual* honest
right-recentered blocker family.

The source is an explicit parameter of the structure, so a closing carrier
can instantiate this type with precisely the source object stored beside its
chart. -/
structure AdaptiveAlignedSmithClosingSourceLatticeData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B) where
  weight : Fin 4 → ℕ
  commonLevel : ℕ
  ramification :
    AdaptiveSmithExposureRamificationData
      weight commonLevel B.aligned.endpoint.defect
  familyIntegrality :
    HasIntegralAdaptiveSmithExposure
      ramification.R weight commonLevel
      B.aligned.endpoint.rightRecenteredFamily
  rightSectionIntegrality :
    HasIntegralAdaptiveSmithSection weight
      (parameterRamificationSection
        (K := K) ramification.R
        B.aligned.endpoint.rightRecenteredRightSection)

namespace AdaptiveAlignedSmithClosingSourceLatticeData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- The actual polynomial family obtained from the retained closing source by
ramification, diagonal source inflation and common-level division. -/
noncomputable def family
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    L.ramification.R L.weight L.commonLevel
    B.aligned.endpoint.rightRecenteredFamily
    L.familyIntegrality

/-- Exact determinant order left on the exposed family. -/
def defect
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) : ℕ :=
  L.ramification.R * B.aligned.endpoint.defect +
    2 * ∑ i : Fin 4, L.weight i - 4 * L.commonLevel

/-- Integral pullback of the ramified zero-left section. -/
noncomputable def leftSection
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection
      (K := K) L.ramification.R
      (zeroPolynomialSection (K := K)))
    (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.ramification.R L.weight)

/-- Integral pullback of the ramified honest right moving section. -/
noncomputable def rightSection
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    Fin 4 → Polynomial K :=
  integralAdaptiveSmithSection L.weight
    (parameterRamificationSection
      (K := K) L.ramification.R
      B.aligned.endpoint.rightRecenteredRightSection)
    L.rightSectionIntegrality

/-- The exposed family carries the exact transformed pure Hessian clock. -/
theorem hessianDefect
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    HasPolynomialFamilyHessianDefect
      (K := K) L.family L.defect := by
  unfold family defect
  exact
    adaptiveSmithExposureFamily_hasHessianDefect
      L.ramification.R L.weight L.commonLevel
      B.aligned.endpoint.defect
      L.ramification rfl
      B.aligned.endpoint.rightRecenteredFamily
      L.familyIntegrality source.hessianDefect

/-- The pulled-back left section is still literally zero. -/
theorem leftSection_eq_zero
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    L.leftSection = zeroPolynomialSection (K := K) := by
  funext i
  let aram :=
    parameterRamificationSection
      (K := K) L.ramification.R
      (zeroPolynomialSection (K := K))
  let hdiv : HasIntegralAdaptiveSmithSection L.weight aram :=
    zeroRamifiedSection_hasIntegralAdaptiveSmithSection
      (K := K) L.ramification.R L.weight
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

/-- The exact moving gradient collision survives the honest lattice exposure. -/
theorem exactCollision
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    HasPolynomialFamilyExactGradientCollision
      L.family L.leftSection L.rightSection := by
  have hram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      L.ramification.R
      B.aligned.endpoint.rightRecenteredFamily
      (zeroPolynomialSection (K := K))
      B.aligned.endpoint.rightRecenteredRightSection
      source.exactCollision
  exact
    polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      L.ramification.R L.weight L.commonLevel
      L.ramification.R_pos
      B.aligned.endpoint.rightRecenteredFamily
      L.familyIntegrality
      (parameterRamificationSection
        (K := K) L.ramification.R
        (zeroPolynomialSection (K := K)))
      (parameterRamificationSection
        (K := K) L.ramification.R
        B.aligned.endpoint.rightRecenteredRightSection)
      (zeroRamifiedSection_hasIntegralAdaptiveSmithSection
        (K := K) L.ramification.R L.weight)
      L.rightSectionIntegrality
      hram

/-- Integrality of the transported marked section forces the longitudinal
source weight to be zero.  This is derived from the actual lattice data and
is not a field of the structure. -/
theorem weight_zero
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    L.weight (0 : Fin 4) = 0 := by
  let bram :=
    parameterRamificationSection
      (K := K) L.ramification.R
      B.aligned.endpoint.rightRecenteredRightSection
  have hconst : Polynomial.constantCoeff (bram (0 : Fin 4)) ≠ 0 := by
    unfold bram parameterRamificationSection
    rw [constantCoeff_parameterRamificationHom
      L.ramification.R L.ramification.R_pos]
    exact
      B.aligned.endpoint.rightRecenteredRightSection_constantCoeff_zero_ne
  exact
    integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
      L.weight bram L.rightSectionIntegrality (0 : Fin 4) hconst

/-- The longitudinal special coordinate of the exposed right section remains
exactly `-1`.  Hence the marked collision cannot collapse during the source
lattice exposure. -/
theorem rightSpecial_zero
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    polynomialSectionSpecialPoint L.rightSection (0 : Fin 4) = -1 := by
  let bram :=
    parameterRamificationSection
      (K := K) L.ramification.R
      B.aligned.endpoint.rightRecenteredRightSection
  have hreinflate :=
    congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        L.weight bram L.rightSectionIntegrality) (0 : Fin 4)
  have hsection : L.rightSection (0 : Fin 4) = bram (0 : Fin 4) := by
    change
      Polynomial.X ^ L.weight (0 : Fin 4) *
          L.rightSection (0 : Fin 4) =
        bram (0 : Fin 4) at hreinflate
    rw [L.weight_zero] at hreinflate
    simpa using hreinflate
  unfold polynomialSectionSpecialPoint
  rw [hsection]
  unfold bram parameterRamificationSection
  rw [constantCoeff_parameterRamificationHom
    L.ramification.R L.ramification.R_pos]
  have h := congrFun
    B.aligned.endpoint.rightRecenteredRightSection_specialPoint
    (0 : Fin 4)
  change
    Polynomial.constantCoeff
        (B.aligned.endpoint.rightRecenteredRightSection (0 : Fin 4)) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) (0 : Fin 4) at h
  simpa [coordinateAxisPoint] using h

/-- The two special points of the exposed moving collision remain distinct.
This uses only the unchanged longitudinal coordinate; transverse quotient
coordinates are allowed to hit a genuine section boundary. -/
theorem specialPoints_ne
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
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

/-- The special fibre of the honest source-lattice exposure carries an actual
distinct exact gradient collision. -/
theorem specialFiber_exactCollision
    (L : AdaptiveAlignedSmithClosingSourceLatticeData B source) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber L.family)
      (polynomialSectionSpecialPoint L.leftSection)
      (polynomialSectionSpecialPoint L.rightSection) := by
  exact
    polynomialFamilyExactGradientCollision_specialFiber
      L.family L.leftSection L.rightSection L.exactCollision

end AdaptiveAlignedSmithClosingSourceLatticeData

/-! ## Terminal defect-zero source lattice -/

/-- A completed source-lattice exposure whose exact transformed Hessian clock
has reached zero.  No endpoint classification is stored here. -/
structure AdaptiveAlignedSmithClosingTerminalLatticeData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B) where
  lattice : AdaptiveAlignedSmithClosingSourceLatticeData B source
  terminalDefect : lattice.defect = 0

namespace AdaptiveAlignedSmithClosingTerminalLatticeData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- The actual associated-graded candidate is simply the special fibre of the
constructed integral source-lattice family. -/
noncomputable def fibre
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber T.lattice.family

/-- Left point of the terminal collision. -/
noncomputable def leftPoint
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) : Fin 4 → K :=
  polynomialSectionSpecialPoint T.lattice.leftSection

/-- Right point of the terminal collision. -/
noncomputable def rightPoint
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) : Fin 4 → K :=
  polynomialSectionSpecialPoint T.lattice.rightSection

/-- Terminal defect zero specializes to the polynomial Monge--Ampere equation
`det Hess = 1`. -/
theorem mongeAmpere
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere T.fibre := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere fibre
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := T.lattice.hessianDefect
  rw [T.terminalDefect] at hdef
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef]
  simp

/-- The terminal fibre carries the actual exact collision. -/
theorem exactCollision
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    HasExactGradientCollision T.fibre T.leftPoint T.rightPoint := by
  exact T.lattice.specialFiber_exactCollision

/-- The terminal collision points are still genuinely distinct. -/
theorem distinct
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    T.leftPoint ≠ T.rightPoint := by
  exact T.lattice.specialPoints_ne

/-- The terminal right point still has longitudinal coordinate `-1`. -/
theorem rightPoint_zero
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    T.rightPoint (0 : Fin 4) = -1 := by
  exact T.lattice.rightSpecial_zero

/-- The terminal left point is exactly zero. -/
theorem leftPoint_eq_zero
    (T : AdaptiveAlignedSmithClosingTerminalLatticeData B source) :
    T.leftPoint = fun _ : Fin 4 => (0 : K) := by
  unfold leftPoint
  rw [T.lattice.leftSection_eq_zero]
  funext i
  simp [polynomialSectionSpecialPoint, zeroPolynomialSection]

end AdaptiveAlignedSmithClosingTerminalLatticeData

/-! ## Closing-carrier-facing aliases -/

/-- Source-lattice data tied to the exact source retained by a rank-one Schur
closing carrier. -/
abbrev AdaptiveAlignedSmithRankOneClosingSourceLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingSourceLatticeData B C.source

/-- Source-lattice data tied to the exact source retained by a zero-Schur
closing carrier. -/
abbrev AdaptiveAlignedSmithZeroSchurClosingSourceLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingSourceLatticeData B C.source

/-- Terminal source-lattice data tied to a rank-one closing carrier. -/
abbrev AdaptiveAlignedSmithRankOneClosingTerminalLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingTerminalLatticeData B C.source

/-- Terminal source-lattice data tied to a zero-Schur closing carrier. -/
abbrev AdaptiveAlignedSmithZeroSchurClosingTerminalLatticeData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B) :=
  AdaptiveAlignedSmithClosingTerminalLatticeData B C.source

end

end HC4.Valuation
