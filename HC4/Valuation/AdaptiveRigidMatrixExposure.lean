import HC4.Valuation.AdaptiveDiagonalExposure
import HC4.Valuation.RigidPacketZeroSchurBridge
import HC4.Valuation.CommonParameterFactorRestart
import Mathlib.Tactic

/-!
# Matrix-level longitudinal exposure for an adaptive rigid packet

The potential itself cannot be given positive longitudinal weight while
retaining the marked points `0` and `e₀`.  After the genuine family and its
collision have already been retained, however, its Hessian matrix may be
placed on the curve

    x₀ = s²,   τ = sʿ

without transforming either marked section.  Conjugation by
`diag(x₀,1,1,1)` aligns the longitudinal orders of a packet
`x₀ⁿ q(x₁,x₂)`.

This file establishes the exact matrix curve and determinant identity.  The
next layer will construct the integral row/column quotient isolating the
minimal packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

variable {K : Type*} [Field K]

/-! ## Longitudinal evaluation with `x₀` retained -/

def rigidLongitudinalSource
    (point : Fin 4 → K)
    (i : Fin 4) : Polynomial K :=
  if i = 0 then Polynomial.X else Polynomial.C (point i)

noncomputable def rigidLongitudinalEval
    (point : Fin 4 → K) :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (rigidLongitudinalSource point)

theorem rigidLongitudinalEval_monomial
    (point : Fin 4 → K)
    (d : Fin 4 →₀ ℕ)
    (a : K) :
    rigidLongitudinalEval point (MvPolynomial.monomial d a) =
      Polynomial.C
          (a * point 1 ^ d 1 * point 2 ^ d 2 * point 3 ^ d 3) *
        Polynomial.X ^ d 0 := by
  classical
  rw [rigidLongitudinalEval, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp [rigidLongitudinalSource, Fin.prod_univ_four]
  ring

/-- A lower bound on every longitudinal source exponent gives the
corresponding univariate divisibility after transverse evaluation. -/
theorem X_pow_dvd_rigidLongitudinalEval_of_support_lowerBound
    (point : Fin 4 → K)
    (G : MvPolynomial (Fin 4) K)
    (k : ℕ)
    (hbound : ∀ d ∈ G.support, k ≤ d 0) :
    Polynomial.X ^ k ∣ rigidLongitudinalEval point G := by
  classical
  rw [G.as_sum, map_sum]
  apply Finset.dvd_sum
  intro d hd
  rw [rigidLongitudinalEval_monomial]
  exact dvd_mul_of_dvd_right
    (polynomial_X_pow_dvd_X_pow_of_le (K := K) k (d 0)
      (hbound d hd)) _

/-- The spatial point obtained by setting the retained longitudinal
coordinate to one. -/
def rigidLongitudinalUnitPoint
    (point : Fin 4 → K)
    (i : Fin 4) : K :=
  if i = 0 then 1 else point i

/-- The coefficient of the retained longitudinal variable at order `k` is
the evaluation at `x₀ = 1` of the exact longitudinal initial form. -/
theorem coeff_rigidLongitudinalEval_eq_eval_initialForm
    (point : Fin 4 → K)
    (G : MvPolynomial (Fin 4) K)
    (k : ℕ) :
    (rigidLongitudinalEval point G).coeff k =
      MvPolynomial.eval (rigidLongitudinalUnitPoint point)
        (HC4.Polynomial.initialForm longitudinalIntegerWeight (k : ℤ) G) := by
  classical
  refine MvPolynomial.induction_on' G ?_ ?_
  · intro d a
    rw [rigidLongitudinalEval_monomial]
    by_cases hdk : d 0 = k
    · subst k
      have hmono :
          MvPolynomial.IsWeightedHomogeneous longitudinalIntegerWeight
            (MvPolynomial.monomial d a) (d 0 : ℤ) := by
        exact MvPolynomial.isWeightedHomogeneous_monomial
          longitudinalIntegerWeight d a (by simp [longitudinalIntegerWeight_eq])
      rw [HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous hmono]
      simp [rigidLongitudinalUnitPoint, MvPolynomial.eval_monomial,
        Finsupp.prod_fintype, Fin.prod_univ_four]
      have hpoly :
          Polynomial.C a * Polynomial.C (point 1) ^ d 1 *
              Polynomial.C (point 2) ^ d 2 * Polynomial.C (point 3) ^ d 3 *
              Polynomial.X ^ d 0 =
              Polynomial.C
                (a * point 1 ^ d 1 * point 2 ^ d 2 * point 3 ^ d 3) *
              Polynomial.X ^ d 0 := by
        simp only [← Polynomial.C_pow, ← Polynomial.C_mul]
      rw [hpoly, Polynomial.coeff_C_mul_X_pow]
      simp
      ring
    · have hmono :
          MvPolynomial.IsWeightedHomogeneous longitudinalIntegerWeight
            (MvPolynomial.monomial d a) (d 0 : ℤ) := by
        exact MvPolynomial.isWeightedHomogeneous_monomial
          longitudinalIntegerWeight d a (by simp [longitudinalIntegerWeight_eq])
      have hweight : (k : ℤ) ≠ (d 0 : ℤ) := by
        exact_mod_cast Ne.symm hdk
      rw [HC4.Polynomial.initialForm_eq_zero_of_isWeightedHomogeneous
        hmono (k : ℤ) hweight]
      simp only [map_zero]
      rw [Polynomial.coeff_C_mul_X_pow]
      have hk : k ≠ d 0 := Ne.symm hdk
      simp [hk]
  · intro p q hp hq
    simp [map_add, hp, hq, HC4.Polynomial.initialForm_add]

/-! ## Separating the positive-parameter remainder -/

/-- Remove the complete constant parameter layer of a polynomial family. -/
noncomputable def positiveParameterRemainder
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  P - constantPolynomialFamily (polynomialFamilySpecialFiber P)

/-- Every coefficient left after removing the special fibre has zero
constant coefficient, hence a common factor of the parameter. -/
theorem positiveParameterRemainder_hasCommonParameterFactor
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasCommonParameterFactor 1 (positiveParameterRemainder P) := by
  intro d hd
  have hcoeff :
      MvPolynomial.coeff d (positiveParameterRemainder P) =
        MvPolynomial.coeff d P -
          Polynomial.C
            (Polynomial.constantCoeff (MvPolynomial.coeff d P)) := by
    unfold positiveParameterRemainder
    rw [MvPolynomial.coeff_sub, coeff_constantPolynomialFamily,
      coeff_polynomialFamilySpecialFiber]
  rw [hcoeff]
  simpa using (Polynomial.X_dvd_iff.mpr (by simp) :
    Polynomial.X ∣
      MvPolynomial.coeff d P -
        Polynomial.C
          (Polynomial.constantCoeff (MvPolynomial.coeff d P)))

/-- Ramification by `R` turns the positive remainder's common parameter
factor into the exact clearance factor `s^R`. -/
theorem parameterRamification_positiveParameterRemainder_hasCommonFactor
    (R : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasCommonParameterFactor R
      (parameterRamificationFamily R (positiveParameterRemainder P)) := by
  have h := parameterRamificationFamily_coefficientDivisibility
    (K := K) R (fun _ : Fin 4 →₀ ℕ => 1)
      (positiveParameterRemainder P)
      (positiveParameterRemainder_hasCommonParameterFactor P)
  simpa [HasCommonParameterFactor, HasParameterCoefficientDivisibility]
    using h

/-- Source value used by the matrix curve: keep the rigid transverse chart
constant and put the longitudinal coordinate on `x₀=s²`. -/
def rigidMatrixCurveSource
    (point : Fin 4 → K)
    (i : Fin 4) : Polynomial K :=
  if i = 0 then Polynomial.X ^ 2 else Polynomial.C (point i)

/-- Simultaneously ramify the family parameter by `R` and place the source
variables on the longitudinal rigid curve. -/
noncomputable def rigidMatrixCurveEval
    (R : ℕ)
    (point : Fin 4 → K) :
    MvPolynomial (Fin 4) (Polynomial K) →+* Polynomial K :=
  MvPolynomial.eval₂Hom
    (parameterRamificationHom (K := K) R)
    (rigidMatrixCurveSource point)

/-- On a family constant in the determinant parameter, the matrix curve is
exactly longitudinal evaluation followed by the square substitution.  The
ramification index `R` is irrelevant on this constant layer. -/
theorem rigidMatrixCurveEval_constantPolynomialFamily
    (R : ℕ)
    (point : Fin 4 → K)
    (G : MvPolynomial (Fin 4) K) :
    rigidMatrixCurveEval R point (constantPolynomialFamily G) =
      parameterRamificationHom (K := K) 2
        (rigidLongitudinalEval point G) := by
  classical
  let f : MvPolynomial (Fin 4) K →+* Polynomial K :=
    (rigidMatrixCurveEval R point).comp (MvPolynomial.map Polynomial.C)
  let g : MvPolynomial (Fin 4) K →+* Polynomial K :=
    (parameterRamificationHom (K := K) 2).comp
      (rigidLongitudinalEval point)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, g, rigidMatrixCurveEval, rigidLongitudinalEval,
        parameterRamificationHom]
    · intro i
      fin_cases i <;>
        simp [f, g, rigidMatrixCurveEval, rigidLongitudinalEval,
          rigidMatrixCurveSource, rigidLongitudinalSource,
          parameterRamificationHom]
  change f G = g G
  exact RingHom.congr_fun hfg G

/-- Hessian of the actual family restricted to the matrix curve. -/
noncomputable def rigidMatrixCurveHessian
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (rigidMatrixCurveEval R point).mapMatrix
    (HC4.Polynomial.hessian P)

/-- Hessian-entry form of
`rigidMatrixCurveEval_constantPolynomialFamily`. -/
theorem rigidMatrixCurveHessian_constantPolynomialFamily
    (R : ℕ)
    (point : Fin 4 → K)
    (G : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    rigidMatrixCurveHessian R point (constantPolynomialFamily G) i j =
      parameterRamificationHom (K := K) 2
        (rigidLongitudinalEval point (HC4.Polynomial.hessian G i j)) := by
  unfold rigidMatrixCurveHessian HC4.Polynomial.hessian
  change rigidMatrixCurveEval R point
      (MvPolynomial.pderiv j
        (MvPolynomial.pderiv i (constantPolynomialFamily G))) = _
  rw [show MvPolynomial.pderiv j
      (MvPolynomial.pderiv i (constantPolynomialFamily G)) =
        constantPolynomialFamily
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i G)) by
    unfold constantPolynomialFamily
    rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]]
  exact rigidMatrixCurveEval_constantPolynomialFamily R point _

/-- Diagonal factor `J=diag(x₀,1,1,1)` after `x₀=s²`. -/
def rigidMatrixLongitudinalShift
    (i : Fin 4) : Polynomial K :=
  if i = 0 then Polynomial.X ^ 2 else 1

/-- The shifted curve Hessian `J H(s²,sʿ) J`. -/
noncomputable def shiftedRigidMatrixCurveHessian
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  fun i j =>
    rigidMatrixLongitudinalShift (K := K) i *
      (rigidMatrixLongitudinalShift (K := K) j *
        rigidMatrixCurveHessian R point P i j)

theorem shiftedRigidMatrixCurveHessian_symmetric
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    ∀ i j,
      shiftedRigidMatrixCurveHessian R point P i j =
        shiftedRigidMatrixCurveHessian R point P j i := by
  intro i j
  have hentry :
      rigidMatrixCurveHessian R point P i j =
        rigidMatrixCurveHessian R point P j i := by
    change rigidMatrixCurveEval R point
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) =
      rigidMatrixCurveEval R point
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j P))
    rw [pderiv_comm_commRing]
  unfold shiftedRigidMatrixCurveHessian
  rw [hentry]
  rw [← mul_assoc, mul_comm
    (rigidMatrixLongitudinalShift (K := K) i)
    (rigidMatrixLongitudinalShift (K := K) j), mul_assoc]

/-- Exact decomposition of the shifted curve Hessian into its constant
special-fibre layer and its positive-parameter remainder. -/
theorem shiftedRigidMatrixCurveHessian_specialFiber_add_remainder
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    shiftedRigidMatrixCurveHessian R point P i j =
      shiftedRigidMatrixCurveHessian R point
          (constantPolynomialFamily (polynomialFamilySpecialFiber P)) i j +
        shiftedRigidMatrixCurveHessian R point
          (positiveParameterRemainder P) i j := by
  have hfamily :
      P = constantPolynomialFamily (polynomialFamilySpecialFiber P) +
        positiveParameterRemainder P := by
    unfold positiveParameterRemainder
    abel
  calc
    shiftedRigidMatrixCurveHessian R point P i j =
        shiftedRigidMatrixCurveHessian R point
          (constantPolynomialFamily (polynomialFamilySpecialFiber P) +
            positiveParameterRemainder P) i j := by
      exact congrArg
        (fun E => shiftedRigidMatrixCurveHessian R point E i j) hfamily
    _ = _ := by
      unfold shiftedRigidMatrixCurveHessian rigidMatrixCurveHessian
      simp [HC4.Polynomial.hessian_apply]
      ring

/-- Every Hessian entry of the positive-parameter remainder acquires the
full ramification factor on the matrix curve. -/
theorem rigidMatrixCurveHessian_positiveParameterRemainder_dvd
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    Polynomial.X ^ R ∣
      rigidMatrixCurveHessian R point (positiveParameterRemainder P) i j := by
  let E := positiveParameterRemainder P
  let hcommon : HasCommonParameterFactor 1 E :=
    positiveParameterRemainder_hasCommonParameterFactor P
  let Q := commonParameterFactorFamily 1 E hcommon
  have hfactor : E = MvPolynomial.C Polynomial.X * Q := by
    simpa using commonParameterFactorFamily_factorisation 1 E hcommon
  have hhess :
      HC4.Polynomial.hessian E i j =
        MvPolynomial.C Polynomial.X *
          HC4.Polynomial.hessian Q i j := by
    rw [hfactor]
    simp [HC4.Polynomial.hessian_apply]
  refine ⟨rigidMatrixCurveEval R point
      (HC4.Polynomial.hessian Q i j), ?_⟩
  unfold rigidMatrixCurveHessian
  change rigidMatrixCurveEval R point
      (HC4.Polynomial.hessian E i j) = _
  rw [hhess, map_mul]
  rw [show rigidMatrixCurveEval R point (MvPolynomial.C Polynomial.X) =
      parameterRamificationHom (K := K) R Polynomial.X by
    simp [rigidMatrixCurveEval]]
  rw [show parameterRamificationHom (K := K) R Polynomial.X =
      Polynomial.X ^ R by
    simpa using parameterRamificationHom_X_pow (K := K) R 1]

/-- The longitudinal congruence does not consume any of the ramification
clearance carried by the positive-parameter Hessian remainder. -/
theorem shiftedRigidMatrixCurveHessian_positiveParameterRemainder_dvd
    (R : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    Polynomial.X ^ R ∣
      shiftedRigidMatrixCurveHessian R point
        (positiveParameterRemainder P) i j := by
  rcases rigidMatrixCurveHessian_positiveParameterRemainder_dvd
      R point P i j with ⟨q, hq⟩
  refine ⟨rigidMatrixLongitudinalShift (K := K) i *
      (rigidMatrixLongitudinalShift (K := K) j * q), ?_⟩
  unfold shiftedRigidMatrixCurveHessian
  rw [hq]
  ring

/-- A ramified factor strictly above the normalization order leaves a
positive residual clock after that normalization. -/
theorem exists_positiveTail_of_X_pow_dvd
    {R e : ℕ}
    {p : Polynomial K}
    (hdiv : Polynomial.X ^ R ∣ p)
    (hlt : e < R) :
    ∃ tail : Polynomial K,
      p = Polynomial.X ^ e * (Polynomial.X * tail) := by
  have hsmall :
      (Polynomial.X : Polynomial K) ^ (e + 1) ∣ Polynomial.X ^ R :=
    polynomial_X_pow_dvd_X_pow_of_le (K := K) (e + 1) R (by omega)
  rcases dvd_trans hsmall hdiv with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  rw [htail, pow_add, pow_one]
  ring

/-! ## Univariate lowest-layer factorisation -/

theorem polynomial_eq_X_pow_mul_C_add_X_mul
    (p : Polynomial K)
    (k : ℕ)
    (c : K)
    (hdiv : Polynomial.X ^ k ∣ p)
    (hcoeff : p.coeff k = c) :
    ∃ tail : Polynomial K,
      p = Polynomial.X ^ k *
        (Polynomial.C c + Polynomial.X * tail) := by
  rcases hdiv with ⟨q, hq⟩
  have hqcoeff : q.coeff 0 = c := by
    rw [← hcoeff, hq, Polynomial.coeff_X_pow_mul']
    simp
  have hXdvd : Polynomial.X ∣ q - Polynomial.C c := by
    apply Polynomial.X_dvd_iff.mpr
    simpa [hqcoeff]
  rcases hXdvd with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  rw [hq]
  congr 1
  linear_combination htail

/-- Square substitution turns the next longitudinal layer into an `s²`
remainder while doubling the leading exponent. -/
theorem parameterRamification_two_lowestLayer_factorisation
    (p : Polynomial K)
    (k : ℕ)
    (c : K)
    (hdiv : Polynomial.X ^ k ∣ p)
    (hcoeff : p.coeff k = c) :
    ∃ tail : Polynomial K,
      parameterRamificationHom (K := K) 2 p =
        Polynomial.X ^ (2 * k) *
          (Polynomial.C c + Polynomial.X ^ 2 * tail) := by
  rcases polynomial_eq_X_pow_mul_C_add_X_mul p k c hdiv hcoeff with
    ⟨tail, htail⟩
  refine ⟨parameterRamificationHom (K := K) 2 tail, ?_⟩
  rw [htail, map_mul, map_add, map_mul]
  simp only [map_pow]
  rw [show parameterRamificationHom (K := K) 2 Polynomial.X =
      Polynomial.X ^ 2 by
    simpa using parameterRamificationHom_X_pow (K := K) 2 1]
  rw [← pow_mul]
  simp [parameterRamificationHom]

/-- Multivariate longitudinal initial-form data converted directly into the
square-curve expansion used by the rigid matrix exposure.  This packages the
support lower bound and the exact initial coefficient, so Hessian entries can
invoke it without repeating univariate bookkeeping. -/
theorem rigidLongitudinalEval_square_lowestLayer_factorisation
    (point : Fin 4 → K)
    (G : MvPolynomial (Fin 4) K)
    (k : ℕ)
    (hbound : ∀ d ∈ G.support, k ≤ d 0) :
    ∃ tail : Polynomial K,
      parameterRamificationHom (K := K) 2
          (rigidLongitudinalEval point G) =
        Polynomial.X ^ (2 * k) *
          (Polynomial.C
              (MvPolynomial.eval (rigidLongitudinalUnitPoint point)
                (HC4.Polynomial.initialForm
                  longitudinalIntegerWeight (k : ℤ) G)) +
            Polynomial.X ^ 2 * tail) := by
  apply parameterRamification_two_lowestLayer_factorisation
  · exact X_pow_dvd_rigidLongitudinalEval_of_support_lowerBound
      point G k hbound
  · exact coeff_rigidLongitudinalEval_eq_eval_initialForm point G k

/-- Natural-valued longitudinal derivative shift: differentiating in
coordinate `0` consumes one longitudinal order, while transverse
derivatives consume none. -/
def rigidLongitudinalDerivativeWeight (i : Fin 4) : ℕ :=
  if i = 0 then 1 else 0

theorem rigidMatrixLongitudinalShift_eq_X_pow_derivativeWeight
    (i : Fin 4) :
    rigidMatrixLongitudinalShift (K := K) i =
      Polynomial.X ^ (2 * rigidLongitudinalDerivativeWeight i) := by
  fin_cases i <;>
    simp [rigidMatrixLongitudinalShift, rigidLongitudinalDerivativeWeight]

/-- The complete special-fibre Hessian expansion supplied by a minimal
longitudinal Smith packet.  This is the Hessian-specific specialization of
`rigidLongitudinalEval_square_lowestLayer_factorisation`; it remains valid
for coordinate `3`, where the selected packet entry is zero. -/
theorem minimalPacket_hessian_square_lowestLayer_factorisation_of_nonnegative
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hD : 2 ≤ D)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (point : Fin 4 → K)
    (i j : Fin 4) :
    rigidLongitudinalDerivativeWeight i +
        rigidLongitudinalDerivativeWeight j ≤ D - 2 →
    let k := D - 2 - rigidLongitudinalDerivativeWeight i -
      rigidLongitudinalDerivativeWeight j
    ∃ tail : Polynomial K,
      parameterRamificationHom (K := K) 2
          (rigidLongitudinalEval point
            (HC4.Polynomial.hessian
              (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j)) =
        Polynomial.X ^ (2 * k) *
          (Polynomial.C
              (MvPolynomial.eval (rigidLongitudinalUnitPoint point)
                (HC4.Polynomial.hessian Q i j)) +
            Polynomial.X ^ 2 * tail) := by
  intro hnonnegative
  dsimp only
  let k := D - 2 - rigidLongitudinalDerivativeWeight i -
    rigidLongitudinalDerivativeWeight j
  have hkcast :
      (k : ℤ) = (D : ℤ) - 2 - longitudinalIntegerWeight i -
        longitudinalIntegerWeight j := by
    unfold k rigidLongitudinalDerivativeWeight longitudinalIntegerWeight
    fin_cases i <;> fin_cases j <;>
      simp [rigidLongitudinalDerivativeWeight] at hnonnegative ⊢ <;> omega
  have hbound :
      ∀ d ∈ (HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j).support,
        k ≤ d 0 := by
    intro d hd
    have hlower := hpacket.hessian_longitudinalWeight_lowerBound
      hquad i j hd
    rw [← hkcast] at hlower
    exact_mod_cast hlower
  rcases rigidLongitudinalEval_square_lowestLayer_factorisation point
      (HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j)
      k hbound with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  rw [htail]
  rw [show HC4.Polynomial.initialForm longitudinalIntegerWeight (k : ℤ)
      (HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j) =
        HC4.Polynomial.hessian Q i j by
    rw [hkcast]
    exact (hpacket.hessian_eq_longitudinalInitialForm
      hD hquad i j).symm]

/-- Uniform wrapper above the cubic boundary. -/
theorem minimalPacket_hessian_square_lowestLayer_factorisation
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hD : 4 ≤ D)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (point : Fin 4 → K)
    (i j : Fin 4) :
    let k := D - 2 - rigidLongitudinalDerivativeWeight i -
      rigidLongitudinalDerivativeWeight j
    ∃ tail : Polynomial K,
      parameterRamificationHom (K := K) 2
          (rigidLongitudinalEval point
            (HC4.Polynomial.hessian
              (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j)) =
        Polynomial.X ^ (2 * k) *
          (Polynomial.C
              (MvPolynomial.eval (rigidLongitudinalUnitPoint point)
                (HC4.Polynomial.hessian Q i j)) +
            Polynomial.X ^ 2 * tail) := by
  apply minimalPacket_hessian_square_lowestLayer_factorisation_of_nonnegative
    hpacket (by omega) hquad point i j
  unfold rigidLongitudinalDerivativeWeight
  fin_cases i <;> fin_cases j <;> simp <;> omega

/-- A packet extracted from the quadratic `(y,z)` Smith subface is
independent of coordinate `3`. -/
theorem minimalPacket_pderiv_three_eq_zero
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    MvPolynomial.pderiv (3 : Fin 4) Q = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_pderiv_backport, MvPolynomial.coeff_zero]
  suffices MvPolynomial.coeff
      (d + Finsupp.single (3 : Fin 4) 1) Q = 0 by simp [this]
  rw [hpacket.packet_eq, coeff_smithSubfaceDegreeComponent]
  split
  · rename_i hmem
    have hs := hquad _ hmem.1
    simp only [smithSupportExponentOf] at hs
    simp [Finsupp.single_apply] at hs
  · rfl

/-- A cubic minimal longitudinal packet has longitudinal exponent exactly
one, so its second longitudinal derivative vanishes. -/
theorem minimalCubicPacket_pderiv_zero_zero_eq_zero
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F 3 Q) :
    MvPolynomial.pderiv (0 : Fin 4)
      (MvPolynomial.pderiv (0 : Fin 4) Q) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_pderiv_backport, coeff_pderiv_backport,
    MvPolynomial.coeff_zero]
  by_cases hcoeff : MvPolynomial.coeff
      ((d + Finsupp.single (0 : Fin 4) 1) +
        Finsupp.single (0 : Fin 4) 1) Q = 0
  · simp [hcoeff]
  · have hx := hpacket.longitudinalExponent _ hcoeff
    simp [Finsupp.single_apply] at hx

/-- The complete mixed quadratic Smith subface, not only its minimal
packet, is independent of coordinate `3`. -/
theorem quadraticSmithSubface_pderiv_three_eq_zero
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    MvPolynomial.pderiv (3 : Fin 4)
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_pderiv_backport, MvPolynomial.coeff_zero,
    coeff_smithSubfacePolynomial]
  split
  · rename_i hmem
    have hs := hquad _ hmem
    simp only [smithSupportExponentOf] at hs
    simp [Finsupp.single_apply] at hs
  · simp

/-- Hessian determinant commutes with specialization of the polynomial
family parameter to zero. -/
theorem hessianDeterminant_polynomialFamilySpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant (polynomialFamilySpecialFiber P) =
      MvPolynomial.map Polynomial.constantCoeff
        (HC4.Polynomial.hessianDeterminant P) := by
  let phi : MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) K := MvPolynomial.map Polynomial.constantCoeff
  unfold HC4.Polynomial.hessianDeterminant polynomialFamilySpecialFiber
  rw [show HC4.Polynomial.hessian (MvPolynomial.map Polynomial.constantCoeff P) =
      (HC4.Polynomial.hessian P).map phi by
    ext i j
    simp [phi, HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]]
  exact (phi.map_det (HC4.Polynomial.hessian P)).symm

/-- A quadratic Smith subface has zero Hessian determinant because its
coordinate-`3` Hessian row vanishes. -/
theorem quadraticSmithSubface_hessianDeterminant_eq_zero
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    HC4.Polynomial.hessianDeterminant
      (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) = 0 := by
  unfold HC4.Polynomial.hessianDeterminant
  apply Matrix.det_eq_zero_of_row_eq_zero (3 : Fin 4)
  intro j
  change MvPolynomial.pderiv j
      (MvPolynomial.pderiv 3
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F)) = 0
  rw [quadraticSmithSubface_pderiv_three_eq_zero hquad]
  simp

/-- A determinant-clock family whose special fibre is a quadratic Smith
subface necessarily has positive defect. -/
theorem quadraticSmithSpecialFiber_hessianDefect_pos
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hspecial : polynomialFamilySpecialFiber P =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    0 < Delta := by
  by_contra hnot
  have hDelta : Delta = 0 := Nat.eq_zero_of_not_pos hnot
  have hzero := quadraticSmithSubface_hessianDeterminant_eq_zero
    (K := K) (F := F) hquad
  rw [← hspecial, hessianDeterminant_polynomialFamilySpecialFiber,
    hdef, hDelta] at hzero
  simp at hzero

theorem minimalPacket_hessian_eval_eq_zero_of_coord_three
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (point : Fin 4 → K)
    (i j : Fin 4)
    (hthree : i = 3 ∨ j = 3) :
    MvPolynomial.eval point (HC4.Polynomial.hessian Q i j) = 0 := by
  rcases hthree with rfl | rfl
  · simp [HC4.Polynomial.hessian_apply,
      minimalPacket_pderiv_three_eq_zero hpacket hquad]
  · change MvPolynomial.eval point
      (MvPolynomial.pderiv 3 (MvPolynomial.pderiv i Q)) = 0
    rw [pderiv_comm_commRing]
    simp [minimalPacket_pderiv_three_eq_zero hpacket hquad]

theorem det_rigidMatrixCurveHessian
    (R Delta : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (rigidMatrixCurveHessian R point P).det =
      Polynomial.X ^ (R * Delta) := by
  have hmap :
      (rigidMatrixCurveHessian R point P).det =
        rigidMatrixCurveEval R point
          (HC4.Polynomial.hessianDeterminant P) := by
    unfold rigidMatrixCurveHessian HC4.Polynomial.hessianDeterminant
    exact (RingHom.map_det
      (rigidMatrixCurveEval R point)
      (HC4.Polynomial.hessian P)).symm
  rw [hmap, hdef]
  simp only [rigidMatrixCurveEval, MvPolynomial.eval₂Hom_C]
  have hX :
      parameterRamificationHom (K := K) R Polynomial.X =
        Polynomial.X ^ R := by
    simpa using parameterRamificationHom_X_pow (K := K) R 1
  rw [map_pow, hX, ← pow_mul]

theorem prod_rigidMatrixLongitudinalShift :
    (∏ i : Fin 4, rigidMatrixLongitudinalShift (K := K) i) =
      Polynomial.X ^ 2 := by
  simp [rigidMatrixLongitudinalShift, Fin.prod_univ_four]

/-- Exact determinant of the shifted matrix curve:

    det(J H(s²,sʿ) J) = s^(RΔ+4).
-/
theorem det_shiftedRigidMatrixCurveHessian
    (R Delta : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (shiftedRigidMatrixCurveHessian R point P).det =
      Polynomial.X ^ (R * Delta + 4) := by
  let v : Fin 4 → Polynomial K :=
    rigidMatrixLongitudinalShift (K := K)
  let A := rigidMatrixCurveHessian R point P
  have hrow :
      (Matrix.det fun i j => v j * A i j) =
        (∏ i : Fin 4, v i) * A.det := by
    exact Matrix.det_mul_row v A
  unfold shiftedRigidMatrixCurveHessian
  change (Matrix.det fun i j => v i * (v j * A i j)) = _
  calc
    (Matrix.det fun i j => v i * (v j * A i j)) =
        (∏ i : Fin 4, v i) *
          (Matrix.det fun i j => v j * A i j) := by
      exact Matrix.det_mul_column v (fun i j => v j * A i j)
    _ = (∏ i : Fin 4, v i) *
          ((∏ i : Fin 4, v i) * A.det) := by rw [hrow]
    _ = (Polynomial.X ^ 2) *
          ((Polynomial.X ^ 2) * Polynomial.X ^ (R * Delta)) := by
      rw [show (∏ i : Fin 4, v i) = Polynomial.X ^ 2 by
        exact prod_rigidMatrixLongitudinalShift]
      rw [det_rigidMatrixCurveHessian R Delta point P hdef]
    _ = Polynomial.X ^ (R * Delta + 4) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

/-! ## Integral normalization of the active three-coordinate block -/

/-- Exponent removed from coordinates `0,1,2`; coordinate `3` is left
unscaled. -/
def rigidMatrixNormalizationExponent
    (n : ℕ)
    (i : Fin 4) : ℕ :=
  if i = 3 then 0 else n

theorem shiftedPositiveParameterRemainder_afterNormalization
    (R n : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hR : 2 * n < R)
    (i j : Fin 4) :
    ∃ tail : Polynomial K,
      shiftedRigidMatrixCurveHessian R point
          (positiveParameterRemainder P) i j =
        Polynomial.X ^
            (rigidMatrixNormalizationExponent n i +
              rigidMatrixNormalizationExponent n j) *
          (Polynomial.X * tail) := by
  apply exists_positiveTail_of_X_pow_dvd
    (shiftedRigidMatrixCurveHessian_positiveParameterRemainder_dvd
      R point P i j)
  unfold rigidMatrixNormalizationExponent
  split <;> split <;> omega

/-- Exact packet-isolation statement needed from the Smith support geometry.
After removing the prescribed row and column powers, the constant entry is
`C i j`; every other contribution has positive matrix-clock order. -/
def HasRigidMatrixPacketIsolation
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ i j, ∃ tail : Polynomial K,
    H i j =
      Polynomial.X ^ rigidMatrixNormalizationExponent n i *
        (Polynomial.X ^ rigidMatrixNormalizationExponent n j *
          (Polynomial.C (C i j) + Polynomial.X * tail))

/-- Final packet-isolation theorem for a retained determinant-clock family
whose special fibre is the mixed quadratic Smith subface.  The minimal
homogeneous packet supplies the constant normalized Hessian matrix, while
all higher special-fibre and positive-parameter terms have positive matrix
clock order. -/
theorem shiftedRigidMatrixCurveHessian_packetIsolation
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {D R : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hspecial : polynomialFamilySpecialFiber P =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hD : 4 ≤ D)
    (hR : 2 * (D - 2) < R) :
    HasRigidMatrixPacketIsolation (D - 2)
      (shiftedRigidMatrixCurveHessian R point P)
      (fun i j => MvPolynomial.eval (rigidLongitudinalUnitPoint point)
        (HC4.Polynomial.hessian Q i j)) := by
  intro i j
  rcases shiftedPositiveParameterRemainder_afterNormalization
      R (D - 2) point P hR i j with ⟨positiveTail, hpositiveTail⟩
  by_cases hthree : i = 3 ∨ j = 3
  · have hpacketZero := minimalPacket_hessian_eval_eq_zero_of_coord_three
      hpacket hquad (rigidLongitudinalUnitPoint point) i j hthree
    have hWderiv := quadraticSmithSubface_pderiv_three_eq_zero
      (K := K) (T := T) (F := F) hquad
    have hWhess : HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j = 0 := by
      rcases hthree with rfl | rfl
      · simp [HC4.Polynomial.hessian_apply, hWderiv]
      · change MvPolynomial.pderiv 3
          (MvPolynomial.pderiv i
            (smithSubfacePolynomial (1 : Fin 4) 2 3 T F)) = 0
        rw [pderiv_comm_commRing]
        simp [hWderiv]
    refine ⟨positiveTail, ?_⟩
    rw [shiftedRigidMatrixCurveHessian_specialFiber_add_remainder,
      hspecial, hpositiveTail]
    unfold shiftedRigidMatrixCurveHessian
    rw [rigidMatrixCurveHessian_constantPolynomialFamily, hWhess]
    simp only [map_zero, mul_zero, zero_add]
    rw [hpacketZero, map_zero, zero_add]
    rw [pow_add]
    ring
  · rcases minimalPacket_hessian_square_lowestLayer_factorisation
        hpacket hD hquad point i j with ⟨specialTail, hspecialTail⟩
    refine ⟨Polynomial.X * specialTail + positiveTail, ?_⟩
    rw [shiftedRigidMatrixCurveHessian_specialFiber_add_remainder,
      hspecial, hpositiveTail]
    unfold shiftedRigidMatrixCurveHessian
    rw [rigidMatrixCurveHessian_constantPolynomialFamily,
      hspecialTail]
    have hi : i ≠ 3 := fun hi => hthree (Or.inl hi)
    have hj : j ≠ 3 := fun hj => hthree (Or.inr hj)
    have hnormi : rigidMatrixNormalizationExponent (D - 2) i = D - 2 := by
      simp [rigidMatrixNormalizationExponent, hi]
    have hnormj : rigidMatrixNormalizationExponent (D - 2) j = D - 2 := by
      simp [rigidMatrixNormalizationExponent, hj]
    have halign :
        2 * rigidLongitudinalDerivativeWeight i +
            (2 * rigidLongitudinalDerivativeWeight j +
              2 * (D - 2 - rigidLongitudinalDerivativeWeight i -
                rigidLongitudinalDerivativeWeight j)) =
          (D - 2) + (D - 2) := by
      unfold rigidLongitudinalDerivativeWeight
      fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega
    rw [rigidMatrixLongitudinalShift_eq_X_pow_derivativeWeight,
      rigidMatrixLongitudinalShift_eq_X_pow_derivativeWeight,
      hnormi, hnormj]
    have hspecialPower :
        Polynomial.X ^ (2 * rigidLongitudinalDerivativeWeight i) *
            (Polynomial.X ^ (2 * rigidLongitudinalDerivativeWeight j) *
              (Polynomial.X ^
                (2 * (D - 2 - rigidLongitudinalDerivativeWeight i -
                  rigidLongitudinalDerivativeWeight j)) *
                (Polynomial.C
                    (MvPolynomial.eval (rigidLongitudinalUnitPoint point)
                      (HC4.Polynomial.hessian Q i j)) +
                  Polynomial.X ^ 2 * specialTail))) =
          Polynomial.X ^ ((D - 2) + (D - 2)) *
            (Polynomial.C
                (MvPolynomial.eval (rigidLongitudinalUnitPoint point)
                  (HC4.Polynomial.hessian Q i j)) +
              Polynomial.X ^ 2 * specialTail) := by
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
      have halign' :
          2 * rigidLongitudinalDerivativeWeight i +
              2 * rigidLongitudinalDerivativeWeight j +
                2 * (D - 2 - rigidLongitudinalDerivativeWeight i -
                  rigidLongitudinalDerivativeWeight j) =
            (D - 2) + (D - 2) := by omega
      rw [halign']
    rw [hspecialPower, pow_add]
    ring

/-- Cubic exceptional packet isolation.  Ramification `R=3` separates all
positive parameter layers.  The sole negative shifted-order entry `(0,0)`
is handled directly: the cubic packet has zero `(0,0)` Hessian entry, while
the two longitudinal congruence factors leave the complete special-fibre
entry at positive normalized order. -/
theorem shiftedRigidMatrixCurveHessian_cubic_packetIsolation
    {T : Finset SmithSupportExponent}
    {F : MvPolynomial (Fin 4) K}
    {Q : MvPolynomial (Fin 4) K}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (hpacket : IsMinimalLongitudinalSmithPacket T F 3 Q)
    (hspecial : polynomialFamilySpecialFiber P =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    HasRigidMatrixPacketIsolation 1
      (shiftedRigidMatrixCurveHessian 3 point P)
      (fun i j => MvPolynomial.eval (rigidLongitudinalUnitPoint point)
        (HC4.Polynomial.hessian Q i j)) := by
  intro i j
  rcases shiftedPositiveParameterRemainder_afterNormalization
      3 1 point P (by omega) i j with ⟨positiveTail, hpositiveTail⟩
  by_cases hthree : i = 3 ∨ j = 3
  · have hpacketZero := minimalPacket_hessian_eval_eq_zero_of_coord_three
      hpacket hquad (rigidLongitudinalUnitPoint point) i j hthree
    have hWderiv := quadraticSmithSubface_pderiv_three_eq_zero
      (K := K) (T := T) (F := F) hquad
    have hWhess : HC4.Polynomial.hessian
        (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) i j = 0 := by
      rcases hthree with rfl | rfl
      · simp [HC4.Polynomial.hessian_apply, hWderiv]
      · change MvPolynomial.pderiv 3
          (MvPolynomial.pderiv i
            (smithSubfacePolynomial (1 : Fin 4) 2 3 T F)) = 0
        rw [pderiv_comm_commRing]
        simp [hWderiv]
    refine ⟨positiveTail, ?_⟩
    rw [shiftedRigidMatrixCurveHessian_specialFiber_add_remainder,
      hspecial, hpositiveTail]
    unfold shiftedRigidMatrixCurveHessian
    rw [rigidMatrixCurveHessian_constantPolynomialFamily, hWhess]
    simp only [map_zero, mul_zero, zero_add]
    rw [hpacketZero, map_zero, zero_add, pow_add]
    ring
  · by_cases hzerozero : i = 0 ∧ j = 0
    · rcases hzerozero with ⟨rfl, rfl⟩
      let S := parameterRamificationHom (K := K) 2
        (rigidLongitudinalEval point
          (HC4.Polynomial.hessian
            (smithSubfacePolynomial (1 : Fin 4) 2 3 T F) 0 0))
      refine ⟨Polynomial.X * S + positiveTail, ?_⟩
      rw [shiftedRigidMatrixCurveHessian_specialFiber_add_remainder,
        hspecial, hpositiveTail]
      unfold shiftedRigidMatrixCurveHessian
      rw [rigidMatrixCurveHessian_constantPolynomialFamily]
      have hQ00 : HC4.Polynomial.hessian Q 0 0 = 0 := by
        exact minimalCubicPacket_pderiv_zero_zero_eq_zero hpacket
      have hQ00eval :
          MvPolynomial.eval (rigidLongitudinalUnitPoint point)
            (HC4.Polynomial.hessian Q 0 0) = 0 := by rw [hQ00]; simp
      simp [rigidMatrixLongitudinalShift,
        rigidMatrixNormalizationExponent, S]
      rw [show MvPolynomial.eval (rigidLongitudinalUnitPoint point)
          (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)) = 0 by
        exact hQ00eval]
      simp
      ring
    · have hnonnegative :
          rigidLongitudinalDerivativeWeight i +
            rigidLongitudinalDerivativeWeight j ≤ 1 := by
        unfold rigidLongitudinalDerivativeWeight
        fin_cases i <;> fin_cases j <;> simp at hthree hzerozero ⊢
      rcases minimalPacket_hessian_square_lowestLayer_factorisation_of_nonnegative
          hpacket (by omega) hquad point i j hnonnegative with
        ⟨specialTail, hspecialTail⟩
      refine ⟨Polynomial.X * specialTail + positiveTail, ?_⟩
      rw [shiftedRigidMatrixCurveHessian_specialFiber_add_remainder,
        hspecial, hpositiveTail]
      unfold shiftedRigidMatrixCurveHessian
      rw [rigidMatrixCurveHessian_constantPolynomialFamily,
        hspecialTail]
      unfold rigidMatrixLongitudinalShift rigidMatrixNormalizationExponent
      fin_cases i <;> fin_cases j <;>
        simp [rigidLongitudinalDerivativeWeight] at hthree hzerozero ⊢ <;>
        ring

/-- Entrywise integrality condition for the congruent normalization. -/
def HasIntegralRigidMatrixNormalization
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K)) : Prop :=
  ∀ i j,
    Polynomial.X ^
        (rigidMatrixNormalizationExponent n i +
          rigidMatrixNormalizationExponent n j) ∣
      H i j

theorem HasRigidMatrixPacketIsolation.integral
    {n : ℕ}
    {H : Matrix (Fin 4) (Fin 4) (Polynomial K)}
    {C : Matrix (Fin 4) (Fin 4) K}
    (hiso : HasRigidMatrixPacketIsolation n H C) :
    HasIntegralRigidMatrixNormalization n H := by
  intro i j
  rcases hiso i j with ⟨tail, htail⟩
  refine ⟨Polynomial.C (C i j) + Polynomial.X * tail, ?_⟩
  rw [htail, ← mul_assoc, ← pow_add]

/-- Chosen integral quotient of one normalized matrix entry. -/
noncomputable def rigidMatrixNormalizedEntry
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H)
    (i j : Fin 4) : Polynomial K :=
  Classical.choose (hdiv i j)

/-- Integral matrix obtained after removing the active row/column factors. -/
noncomputable def integralRigidMatrixNormalization
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  fun i j => rigidMatrixNormalizedEntry n H hdiv i j

theorem rigidMatrixNormalizedEntry_spec
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H)
    (i j : Fin 4) :
    H i j =
      Polynomial.X ^ rigidMatrixNormalizationExponent n i *
        (Polynomial.X ^ rigidMatrixNormalizationExponent n j *
          integralRigidMatrixNormalization n H hdiv i j) := by
  have hspec := Classical.choose_spec (hdiv i j)
  unfold integralRigidMatrixNormalization rigidMatrixNormalizedEntry
  rw [← mul_assoc, ← pow_add]
  exact hspec

/-- Packet isolation identifies the constant coefficient of the chosen
integral quotient.  The proof cancels the nonzero monomial normalization, so
it is independent of the noncomputable choice of quotient. -/
theorem constantCoeff_integralRigidMatrixNormalization
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hiso : HasRigidMatrixPacketIsolation n H C)
    (i j : Fin 4) :
    Polynomial.constantCoeff
        (integralRigidMatrixNormalization n H hiso.integral i j) =
      C i j := by
  rcases hiso i j with ⟨tail, htail⟩
  have hspec := rigidMatrixNormalizedEntry_spec n H hiso.integral i j
  have heq :
      Polynomial.X ^
          (rigidMatrixNormalizationExponent n i +
            rigidMatrixNormalizationExponent n j) *
          integralRigidMatrixNormalization n H hiso.integral i j =
        Polynomial.X ^
          (rigidMatrixNormalizationExponent n i +
            rigidMatrixNormalizationExponent n j) *
          (Polynomial.C (C i j) + Polynomial.X * tail) := by
    calc
      _ = H i j := by
        simpa [← mul_assoc, ← pow_add] using hspec.symm
      _ = _ := by
        simpa [← mul_assoc, ← pow_add] using htail
  have hcancel :
      integralRigidMatrixNormalization n H hiso.integral i j =
        Polynomial.C (C i j) + Polynomial.X * tail := by
    exact mul_left_cancel₀
      (pow_ne_zero
        (rigidMatrixNormalizationExponent n i +
          rigidMatrixNormalizationExponent n j)
        Polynomial.X_ne_zero)
      heq
  rw [hcancel]
  simp

/-- Symmetry survives the integral normalization. -/
theorem integralRigidMatrixNormalization_symmetric
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H)
    (hsymm : ∀ i j, H i j = H j i) :
    ∀ i j,
      integralRigidMatrixNormalization n H hdiv i j =
        integralRigidMatrixNormalization n H hdiv j i := by
  intro i j
  have hij := rigidMatrixNormalizedEntry_spec n H hdiv i j
  have hji := rigidMatrixNormalizedEntry_spec n H hdiv j i
  have heq :
      Polynomial.X ^
          (rigidMatrixNormalizationExponent n i +
            rigidMatrixNormalizationExponent n j) *
          integralRigidMatrixNormalization n H hdiv i j =
        Polynomial.X ^
          (rigidMatrixNormalizationExponent n i +
            rigidMatrixNormalizationExponent n j) *
          integralRigidMatrixNormalization n H hdiv j i := by
    calc
      _ = H i j := by
        simpa [← mul_assoc, ← pow_add] using hij.symm
      _ = H j i := hsymm i j
      _ = _ := by
        simpa [← mul_assoc, ← pow_add, Nat.add_comm] using hji
  exact mul_left_cancel₀
    (pow_ne_zero
      (rigidMatrixNormalizationExponent n i +
        rigidMatrixNormalizationExponent n j)
      Polynomial.X_ne_zero)
    heq

/-- Four-block carried by the normalized symmetric matrix. -/
noncomputable def isolatedRigidMatrixFourBlock
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H) :
    GeneralFourBlock (Polynomial K) :=
  GeneralFourBlock.ofSymmetricMatrix
    (integralRigidMatrixNormalization n H hdiv)

theorem constantCoeffFourBlock_isolatedRigidMatrixFourBlock
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hiso : HasRigidMatrixPacketIsolation n H C) :
    constantCoeffFourBlock
        (isolatedRigidMatrixFourBlock n H hiso.integral) =
      GeneralFourBlock.ofSymmetricMatrix C := by
  ext <;>
    exact constantCoeff_integralRigidMatrixNormalization n H C hiso _ _

/-- Once the geometric support argument supplies packet isolation, the
existing zero-Schur interface follows without rebuilding any Schur algebra. -/
noncomputable def exactZeroSchurFourBlockData_of_packetIsolation
    (n defect : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hiso : HasRigidMatrixPacketIsolation n H C)
    (hsymm : ∀ i j, H i j = H j i)
    (hdet :
      (integralRigidMatrixNormalization n H hiso.integral).det =
        Polynomial.X ^ defect)
    (hchart :
      (GeneralFourBlock.ofSymmetricMatrix C).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurC = 0) :
    ExactZeroSchurFourBlockData K := by
  let B := isolatedRigidMatrixFourBlock n H hiso.integral
  have hBmatrix :
      B.matrix = integralRigidMatrixNormalization n H hiso.integral := by
    exact GeneralFourBlock.matrix_ofSymmetricMatrix _
      (integralRigidMatrixNormalization_symmetric n H hiso.integral hsymm)
  have hconstant :
      constantCoeffFourBlock B = GeneralFourBlock.ofSymmetricMatrix C :=
    constantCoeffFourBlock_isolatedRigidMatrixFourBlock n H C hiso
  refine {
    block := B
    defect := defect
    fullDet := ?_
    activeDet_coeff_zero_ne_zero := ?_
    schurA_coeff_zero := ?_
    schurB_coeff_zero := ?_
    schurC_coeff_zero := ?_
  }
  · rw [← GeneralFourBlock.matrix_det, hBmatrix]
    exact hdet
  · rw [constantCoeffFourBlock_activeDet, hconstant]
    exact hchart.1
  · rw [constantCoeffFourBlock_schurA, hconstant]
    exact hchart.2.1
  · rw [constantCoeffFourBlock_schurB, hconstant]
    exact hchart.2.2.1
  · rw [constantCoeffFourBlock_schurC, hconstant]
    exact hchart.2.2.2

theorem prod_rigidMatrixNormalizationFactor
    (n : ℕ) :
    (∏ i : Fin 4,
        (Polynomial.X : Polynomial K) ^
          rigidMatrixNormalizationExponent n i) =
      Polynomial.X ^ (3 * n) := by
  simp [rigidMatrixNormalizationExponent, Fin.prod_univ_four]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- Reinflating the normalized matrix multiplies its determinant by
`s^(6n)`. -/
theorem det_eq_normalizationFactor_mul_det
    (n : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H) :
    H.det = Polynomial.X ^ (6 * n) *
      (integralRigidMatrixNormalization n H hdiv).det := by
  let v : Fin 4 → Polynomial K := fun i =>
    Polynomial.X ^ rigidMatrixNormalizationExponent n i
  let Q := integralRigidMatrixNormalization n H hdiv
  have hmatrix : H = fun i j => v i * (v j * Q i j) := by
    apply Matrix.ext
    intro i j
    exact rigidMatrixNormalizedEntry_spec n H hdiv i j
  have hrow :
      (Matrix.det fun i j => v j * Q i j) =
        (∏ i : Fin 4, v i) * Q.det := by
    exact Matrix.det_mul_row v Q
  calc
    H.det = (Matrix.det fun i j => v i * (v j * Q i j)) :=
      congrArg Matrix.det hmatrix
    _ =
        (∏ i : Fin 4, v i) *
          (Matrix.det fun i j => v j * Q i j) := by
      exact Matrix.det_mul_column v (fun i j => v j * Q i j)
    _ = (∏ i : Fin 4, v i) *
          ((∏ i : Fin 4, v i) * Q.det) := by rw [hrow]
    _ = Polynomial.X ^ (6 * n) * Q.det := by
      rw [show (∏ i : Fin 4, v i) = Polynomial.X ^ (3 * n) by
        exact prod_rigidMatrixNormalizationFactor n]
      rw [← mul_assoc, ← pow_add]
      congr 1
      ring

/-- Exact clock after an integral active-three-coordinate normalization. -/
theorem det_integralRigidMatrixNormalization_eq_X_pow_sub
    (n N : ℕ)
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (hdiv : HasIntegralRigidMatrixNormalization n H)
    (hdet : H.det = Polynomial.X ^ N)
    (hle : 6 * n ≤ N) :
    (integralRigidMatrixNormalization n H hdiv).det =
      Polynomial.X ^ (N - 6 * n) := by
  have hfactor := det_eq_normalizationFactor_mul_det n H hdiv
  rw [hdet] at hfactor
  have hpow :
      (Polynomial.X : Polynomial K) ^ N =
        Polynomial.X ^ (6 * n) * Polynomial.X ^ (N - 6 * n) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hfactor
  exact mul_left_cancel₀ (pow_ne_zero (6 * n) Polynomial.X_ne_zero) hfactor.symm

/-- Specialization to the shifted matrix curve. -/
theorem det_normalizedShiftedRigidMatrixCurveHessian
    (R Delta n : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hdiv : HasIntegralRigidMatrixNormalization n
      (shiftedRigidMatrixCurveHessian R point P))
    (hle : 6 * n ≤ R * Delta + 4) :
    (integralRigidMatrixNormalization n
      (shiftedRigidMatrixCurveHessian R point P) hdiv).det =
      Polynomial.X ^ (R * Delta + 4 - 6 * n) := by
  exact det_integralRigidMatrixNormalization_eq_X_pow_sub
    n (R * Delta + 4) _ hdiv
      (det_shiftedRigidMatrixCurveHessian R Delta point P hdef) hle

/-- Direct handoff from a geometrically isolated packet on the shifted
family Hessian to the existing zero-Schur clock interface. -/
noncomputable def adaptiveRigidMatrixZeroSchurData
    (R Delta n : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hiso : HasRigidMatrixPacketIsolation n
      (shiftedRigidMatrixCurveHessian R point P) C)
    (hle : 6 * n ≤ R * Delta + 4)
    (hchart :
      (GeneralFourBlock.ofSymmetricMatrix C).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurC = 0) :
    ExactZeroSchurFourBlockData K :=
  exactZeroSchurFourBlockData_of_packetIsolation
    n (R * Delta + 4 - 6 * n)
    (shiftedRigidMatrixCurveHessian R point P) C hiso
    (shiftedRigidMatrixCurveHessian_symmetric R point P)
    (det_normalizedShiftedRigidMatrixCurveHessian
      R Delta n point P hdef hiso.integral hle)
    hchart

/-- Cubic rigid continuation sealed through the existing exact zero-Schur
interface.  Positivity of the original defect supplies the normalization
inequality `6 ≤ 3*Δ+4`. -/
noncomputable def cubicAdaptiveRigidMatrixZeroSchurData
    {T : Finset SmithSupportExponent}
    {F Q : MvPolynomial (Fin 4) K}
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hpacket : IsMinimalLongitudinalSmithPacket T F 3 Q)
    (hspecial : polynomialFamilySpecialFiber P =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hchart :
      let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
        MvPolynomial.eval (rigidLongitudinalUnitPoint point)
          (HC4.Polynomial.hessian Q i j)
      (GeneralFourBlock.ofSymmetricMatrix C).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurC = 0) :
    ExactZeroSchurFourBlockData K := by
  let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
    MvPolynomial.eval (rigidLongitudinalUnitPoint point)
      (HC4.Polynomial.hessian Q i j)
  have hDelta := quadraticSmithSpecialFiber_hessianDefect_pos
    hdef hspecial hquad
  exact adaptiveRigidMatrixZeroSchurData 3 Delta 1 point P C hdef
    (shiftedRigidMatrixCurveHessian_cubic_packetIsolation
      P point hpacket hspecial hquad)
    (by omega) hchart

/-- Rigid continuation above the cubic boundary, sealed through the exact
zero-Schur interface with the canonical scale `R=6D-16`. -/
noncomputable def higherAdaptiveRigidMatrixZeroSchurData
    {T : Finset SmithSupportExponent}
    {F Q : MvPolynomial (Fin 4) K}
    (D Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (hD : 4 ≤ D)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hpacket : IsMinimalLongitudinalSmithPacket T F D Q)
    (hspecial : polynomialFamilySpecialFiber P =
      smithSubfacePolynomial (1 : Fin 4) 2 3 T F)
    (hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0))
    (hchart :
      let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
        MvPolynomial.eval (rigidLongitudinalUnitPoint point)
          (HC4.Polynomial.hessian Q i j)
      (GeneralFourBlock.ofSymmetricMatrix C).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurC = 0) :
    ExactZeroSchurFourBlockData K := by
  let R := 6 * D - 16
  let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
    MvPolynomial.eval (rigidLongitudinalUnitPoint point)
      (HC4.Polynomial.hessian Q i j)
  have hDelta := quadraticSmithSpecialFiber_hessianDefect_pos
    hdef hspecial hquad
  exact adaptiveRigidMatrixZeroSchurData R Delta (D - 2) point P C hdef
    (shiftedRigidMatrixCurveHessian_packetIsolation P point hpacket
      hspecial hquad hD
      (by unfold R; omega))
    (by
      have hRle : R ≤ R * Delta := Nat.le_mul_of_pos_right R hDelta
      calc
        6 * (D - 2) = R + 4 := by unfold R; omega
        _ ≤ R * Delta + 4 := Nat.add_le_add_right hRle 4)
    hchart

/-! ## Canonical clock arithmetic above the cubic boundary -/

theorem canonicalRigidMatrixRamification_gt_twice_packetOrder
    (D : ℕ)
    (hD : 4 ≤ D) :
    2 * (D - 2) < 6 * D - 16 := by
  omega

/-- With `R=6D-16`, the normalized matrix clock is exactly the scaled
presentation `R*(Δ-1)` for every `D≥4`. -/
theorem canonicalRigidMatrixExposureExponent_eq
    (D Delta : ℕ)
    (hD : 4 ≤ D) :
    (6 * D - 16) * Delta + 4 - 6 * (D - 2) =
      (6 * D - 16) * (Delta - 1) := by
  cases Delta with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_sub]
      omega
  | succ delta =>
      simp only [Nat.succ_sub_one]
      have hcost : 6 * D - 16 + 4 = 6 * (D - 2) := by omega
      calc
        (6 * D - 16) * (delta + 1) + 4 - 6 * (D - 2) =
            (6 * D - 16) * delta +
              ((6 * D - 16) + 4) - 6 * (D - 2) := by ring
        _ = (6 * D - 16) * delta := by omega

/-- The cubic matrix exposure uses scale `3` and raw normalized determinant
order `3*Δ-2 = 3*(Δ-1)+1`.  Euclidean normalization therefore gives the
strict natural-valued predecessor exactly. -/
theorem cubicRigidMatrixExposure_div_scale_eq_pred
    (Delta : ℕ) :
    (3 * Delta + 4 - 6) / 3 = Delta - 1 := by
  cases Delta with
  | zero => norm_num
  | succ delta =>
      simp only [Nat.succ_sub_one]
      have hexp : 3 * (delta + 1) + 4 - 6 = 3 * delta + 1 := by omega
      rw [hexp, Nat.add_div (by norm_num : 0 < 3)]
      norm_num

end

end HC4.Valuation
