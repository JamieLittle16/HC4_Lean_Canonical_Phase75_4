import HC4.Valuation.AdaptiveAlignedSmithClosingFirstContactLattice
import HC4.Newton.TerminalDirectRankJumpReduction
import Mathlib.Tactic

/-!
# First-contact exposure weight versus terminal cocharacter

A genuine positive first contact is selected in the extended
`(parameter order, source exponent)` Newton space:

    R * q + weight_W(d) = commonLevel,    q > 0.

Consequently the visible contact monomial has strictly smaller *source*
`W`-weight than `commonLevel`.  Thus the exposure weight used to create the
first-contact special fibre cannot itself be the homogeneous terminal
cocharacter of that fibre.

This file records that distinction explicitly and introduces the correct
source-level terminal-cocharacter carrier.  The terminal cocharacter is a
second nonnegative integral source scaling on the already constructed
first-contact fibre.  It is required to transport the marked right point
honestly.  Since that point has longitudinal coordinate `-1`, integrality
forces terminal weight zero on the marked longitudinal coordinate.

The first-contact terminal fibre is already a genuine polynomial
Monge--Ampère solution with a distinct exact gradient collision.  Hence its
actual Hessian at the origin is nondegenerate.  Any nontrivial homogeneous
terminal cocharacter therefore enters the existing direct-rank-jump
dichotomy; the exact collision eliminates the scalar branch.  The result is
a genuine non-scalar conformal terminal face with a marked zero coordinate.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## The first-contact exposure weight is not a terminal homogeneous weight -/

/-- Support-level natural weighted homogeneity for the source weight used by
an adaptive Smith exposure.  This deliberately stays in `ℕ`; the terminal
cocharacter below is a separate object and is stored in the integral
weighted-homogeneity API used by the terminal theory. -/
def IsAdaptiveSmithSourceWeightHomogeneous
    (W : Fin 4 → ℕ)
    (m : ℕ)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d : Fin 4 →₀ ℕ,
    MvPolynomial.coeff d F ≠ 0 →
      Finsupp.weight W d = m

namespace AdaptiveAlignedSmithClosingFirstContactLatticeData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- A genuine positive first contact has source weight strictly below the
divided level.  The missing amount is exactly the positive parameter
contribution `R*q`. -/
theorem contactSourceWeight_lt_commonLevel
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    Finsupp.weight L.weight L.contactExponent < L.commonLevel := by
  let q :=
    smithFamilyCoefficientParameterOrder
      B.aligned.endpoint.rightRecenteredFamily
      L.contactExponent L.contactSupport
  have hq : 0 < q := by
    simpa [q] using L.contactOrderPositive
  have hR : 0 < L.R := L.R_pos
  have hRq : 0 < L.R * q := Nat.mul_pos hR hq
  have heq :
      L.R * q + Finsupp.weight L.weight L.contactExponent =
        L.commonLevel := by
    simpa [q] using L.contactLevel
  omega

/-- Therefore the first-contact special fibre is *not* homogeneous of the
divided level for the exposure source weight.  This is the formal reason the
first-contact lattice weight must not be identified with the terminal
cocharacter. -/
theorem specialFiber_not_sourceWeightHomogeneous
    (L : AdaptiveAlignedSmithClosingFirstContactLatticeData B source) :
    ¬ IsAdaptiveSmithSourceWeightHomogeneous
        L.weight L.commonLevel
        (polynomialFamilySpecialFiber L.family) := by
  intro hhom
  have heq :=
    hhom L.contactExponent L.contactCoefficient_specialFiber_ne_zero
  exact (Nat.ne_of_lt L.contactSourceWeight_lt_commonLevel) heq

end AdaptiveAlignedSmithClosingFirstContactLatticeData

namespace AdaptiveAlignedSmithClosingFirstContactTerminalData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}

/-- Terminal first contact still cannot be homogeneous for its *exposure*
source weight at the exposure divided level. -/
theorem not_sourceWeightHomogeneous
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    ¬ IsAdaptiveSmithSourceWeightHomogeneous
        T.lattice.weight T.lattice.commonLevel T.fibre := by
  simpa [fibre] using
    T.lattice.specialFiber_not_sourceWeightHomogeneous

/-- The actual Hessian of a terminal first-contact Monge--Ampère fibre is
nondegenerate at the origin. -/
theorem mongeAmpere_hasNondegenerateActualHessian
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    HasNondegenerateTerminalActualHessian
      (0 : Fin 4) 1 2 3 T.fibre := by
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

end AdaptiveAlignedSmithClosingFirstContactTerminalData

/-! ## Honest terminal cocharacter on the first-contact fibre -/

/-- Constant polynomial section attached to the terminal right special point. -/
noncomputable def firstContactTerminalRightConstantSection
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) :
    Fin 4 → Polynomial K :=
  polynomialConstantSection T.rightPoint

/-- A genuine terminal source cocharacter on the already constructed
first-contact fibre.

This is intentionally separate from `T.lattice.weight`: positive first
contact proves that the latter cannot be the terminal homogeneous weight.

The extra `rightPointIntegrality` field says the terminal diagonal source
scaling really transports the marked collision point.  It is the honest
source-lattice input that forces the marked longitudinal terminal weight to
remain zero. -/
structure AdaptiveAlignedSmithFirstContactTerminalCocharacterData
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
    (T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source) where
  weight : Fin 4 → ℕ
  degree : ℕ
  nontrivial :
    IsNontrivialIntegralWeight (fun i => (weight i : ℤ))
  homogeneous :
    IsIntegralWeightedHomogeneous
      (fun i => (weight i : ℤ)) (degree : ℤ) T.fibre
  rightPointIntegrality :
    HasIntegralAdaptiveSmithSection
      weight (firstContactTerminalRightConstantSection T)

namespace AdaptiveAlignedSmithFirstContactTerminalCocharacterData

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
variable {source : AdaptiveAlignedSmithBlockerRecenteredSourceData B}
variable {T : AdaptiveAlignedSmithClosingFirstContactTerminalData B source}

/-- The integral terminal cocharacter is automatically nonnegative. -/
theorem nonnegative
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    IsNonnegativeIntegralWeight (fun i => (C.weight i : ℤ)) := by
  intro i
  show (0 : ℤ) ≤ (C.weight i : ℤ)
  exact Int.ofNat_nonneg (C.weight i)

/-- Honest transport of the marked right point forces terminal weight zero
on the longitudinal coordinate. -/
theorem weight_zero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    C.weight (0 : Fin 4) = 0 := by
  apply
    integralAdaptiveSmithSection_weight_eq_zero_of_constantCoeff_ne_zero
      C.weight
      (firstContactTerminalRightConstantSection T)
      C.rightPointIntegrality
      (0 : Fin 4)
  unfold firstContactTerminalRightConstantSection
  simp [polynomialConstantSection, T.rightPoint_zero]

/-- Integral form of the marked terminal zero-weight statement. -/
theorem integralWeight_zero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    (fun i => (C.weight i : ℤ)) (0 : Fin 4) = 0 := by
  simp [C.weight_zero]

/-- The terminal first-contact collision eliminates the scalar branch of the
direct-rank-jump dichotomy.  Hence every honest nontrivial terminal
cocharacter on this fibre is genuinely non-scalar and conformal. -/
theorem residualNonScalarJump
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    HasResidualNonScalarTerminalJump
      (fun i => (C.weight i : ℤ))
      (C.degree : ℤ)
      T.fibre := by
  exact
    terminalDirectRankJump_collision_forces_residual
      C.nontrivial
      C.homogeneous
      T.mongeAmpere_hasNondegenerateActualHessian
      T.leftPoint T.rightPoint
      T.distinct
      T.exactCollision

/-- In particular the terminal cocharacter lies on a genuine zero-weight
boundary: the marked longitudinal coordinate is one such zero. -/
theorem hasZeroWeight
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    HasTerminalZeroWeight (fun i => (C.weight i : ℤ)) := by
  exact ⟨0, C.integralWeight_zero⟩

/-- The residual terminal face is non-scalar, nonnegative, and already comes
with the distinguished zero coordinate.  Thus the only remaining
weight-pattern issue is whether some *second* coordinate also has weight
zero. -/
theorem residual_nonnegative_markedZero
    (C : AdaptiveAlignedSmithFirstContactTerminalCocharacterData T) :
    HasResidualNonScalarTerminalJump
        (fun i => (C.weight i : ℤ))
        (C.degree : ℤ)
        T.fibre ∧
      IsNonnegativeIntegralWeight
        (fun i => (C.weight i : ℤ)) ∧
      (fun i => (C.weight i : ℤ)) (0 : Fin 4) = 0 := by
  exact ⟨C.residualNonScalarJump, C.nonnegative, C.integralWeight_zero⟩

end AdaptiveAlignedSmithFirstContactTerminalCocharacterData

end

end HC4.Valuation
