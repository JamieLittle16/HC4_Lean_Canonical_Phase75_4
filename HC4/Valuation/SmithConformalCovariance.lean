import HC4.Valuation.IntegralKernelSlopeExtraction
import HC4.Newton.SmithValuationTiltAdapter
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Integral Smith conformal covariance

The finite Smith pole-minimality package is phrased in terms of the two
relative Levi grades

    Gamma = (b+d-1, c+d-1).

To use that package in the global restart argument, a Smith separator must
be realised by an *actual integral polynomial transformation*, not merely
by an abstract valuation inequality.

For nonnegative integral tilt parameters `(theta1, theta2)`, put

    D = diag(1, tau^theta1, tau^theta2, tau^(theta1+theta2))

and let the conformal multiplier be

    mu = tau^(theta1+theta2).

The normalised Smith transform is formally

    Q(Y) = mu^(-1) P(DY).

We never form negative powers.  Instead, for every source monomial we ask
that its coefficient after the honest source inflation by `D` be divisible
by `mu`, choose the quotient coefficient, and reconstruct `Q` over `K[tau]`.

This file proves:

* the coefficientwise integral construction;
* the exact polynomial identity `Inflate(P) = C(mu) * Q`;
* the formal chain rule for the two-parameter diagonal inflation;
* exact Hessian-determinant covariance;
* exact preservation of a pure determinant defect;
* integral transformation of marked polynomial sections;
* exact gradient-collision covariance.

Thus every denominator-cleared Smith separator satisfying the finite
divisibility conditions is an honest determinant-preserving conformal Rees
move.  No Laurent-polynomial or restart hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open scoped BigOperators
open HC4.Newton

variable {K : Type*} [Field K]

/-! ## The Smith diagonal and its valuation meaning -/

/-- Exponent of `tau` multiplying one source variable under the canonical
Smith conformal inflation.  The ordered Smith coordinates are
`(x,y,z,w) = (0,1,2,3)`. -/
def smithConformalSourceExponent
    (theta1 theta2 : ℕ)
    (i : Fin 4) : ℕ :=
  if i = 0 then
    0
  else if i = 1 then
    theta1
  else if i = 2 then
    theta2
  else
    theta1 + theta2

/-- Exponent of the conformal multiplier. -/
def smithConformalMultiplierExponent
    (theta1 theta2 : ℕ) : ℕ :=
  theta1 + theta2

/-- Raw source exponent contributed to a monomial
`x^a y^b z^c w^d`. -/
def smithConformalRawExponent
    (theta1 theta2 : ℕ)
    (d : Fin 4 →₀ ℕ) : ℕ :=
  theta1 * d 1 +
    theta2 * d 2 +
    (theta1 + theta2) * d 3

/-- The raw exponent minus the multiplier exponent is exactly the already
formalised Smith normalised valuation change. -/
theorem smithConformalRawExponent_sub_multiplier_eq_gradeChange
    (theta1 theta2 : ℕ)
    (d : Fin 4 →₀ ℕ) :
    (smithConformalRawExponent theta1 theta2 d : ℤ) -
        (smithConformalMultiplierExponent theta1 theta2 : ℤ) =
      smithNormalisedConformalTiltChange
        ((theta1 : ℤ), (theta2 : ℤ))
        (d 1) (d 2) (d 3) := by
  unfold smithConformalRawExponent
  unfold smithConformalMultiplierExponent
  unfold smithNormalisedConformalTiltChange
  unfold smithRawConformalTiltChange
  unfold smithLeviNormalisationTiltChange
  push_cast
  ring

/-- Hence the same exponent difference is the dot product with the Smith
relative Levi grade. -/
theorem smithConformalRawExponent_sub_multiplier_eq_gradeDot
    (theta1 theta2 : ℕ)
    (d : Fin 4 →₀ ℕ) :
    (smithConformalRawExponent theta1 theta2 d : ℤ) -
        (smithConformalMultiplierExponent theta1 theta2 : ℤ) =
      smithGradeDot
        ((theta1 : ℤ), (theta2 : ℤ))
        (smithGrade (d 1) (d 2) (d 3)) := by
  rw [smithConformalRawExponent_sub_multiplier_eq_gradeChange]
  exact
    smithNormalisedConformalTiltChange_eq_gradeDot
      ((theta1 : ℤ), (theta2 : ℤ))
      (d 1) (d 2) (d 3)

/-! ## Honest source inflation -/

/-- Polynomial chain-rule coefficient attached to source coordinate `i`. -/
def smithConformalDerivativeCoefficient
    (theta1 theta2 : ℕ)
    (i : Fin 4) :
    Polynomial K :=
  Polynomial.X ^
    smithConformalSourceExponent theta1 theta2 i

/-- The conformal multiplier as a polynomial in the Rees parameter. -/
def smithConformalMultiplier
    (theta1 theta2 : ℕ) :
    Polynomial K :=
  Polynomial.X ^
    smithConformalMultiplierExponent theta1 theta2

/-- Product of the source diagonal factors contributed by one source
monomial exponent. -/
def smithConformalCoefficientFactor
    (theta1 theta2 : ℕ)
    (d : Fin 4 →₀ ℕ) :
    Polynomial K :=
  ∏ i : Fin 4,
    smithConformalDerivativeCoefficient
      (K := K) theta1 theta2 i ^ d i

/-- The honest integral source change on a polynomial section. -/
def smithConformalInflateSection
    (theta1 theta2 : ℕ)
    (a : Fin 4 → Polynomial K) :
    Fin 4 → Polynomial K :=
  fun i =>
    smithConformalDerivativeCoefficient
        (K := K) theta1 theta2 i *
      a i

/-- Image of one source variable under the Smith diagonal inflation. -/
def smithConformalInflateVariable
    (theta1 theta2 : ℕ)
    (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.C
      (smithConformalDerivativeCoefficient
        (K := K) theta1 theta2 i) *
    MvPolynomial.X i

/-- Honest polynomial-ring source substitution by the Smith diagonal. -/
noncomputable def smithConformalInflateHom
    (theta1 theta2 : ℕ) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom
    MvPolynomial.C
    (smithConformalInflateVariable
      (K := K) theta1 theta2)

/-- Evaluation semantics of the Smith source inflation. -/
theorem eval_smithConformalInflateHom
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval a
        (smithConformalInflateHom
          (K := K) theta1 theta2 P) =
      MvPolynomial.eval
        (smithConformalInflateSection
          theta1 theta2 a)
        P := by
  change
    MvPolynomial.eval a
        (MvPolynomial.eval₂
          MvPolynomial.C
          (smithConformalInflateVariable
            (K := K) theta1 theta2)
          P) =
      MvPolynomial.eval
        (smithConformalInflateSection
          theta1 theta2 a)
        P
  rw [← MvPolynomial.eval_assoc
    (smithConformalInflateVariable
      (K := K) theta1 theta2)
    a P]
  apply congrArg (fun x =>
    MvPolynomial.eval x P)
  funext i
  simp [smithConformalInflateVariable,
    smithConformalInflateSection]

/-- Product identity for one source monomial under the Smith diagonal. -/
theorem fin4_smithConformalInflateSection_monomialProduct
    (theta1 theta2 : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ) :
    (∏ i : Fin 4,
        smithConformalInflateSection
          theta1 theta2 a i ^ d i) =
      smithConformalCoefficientFactor
          (K := K) theta1 theta2 d *
        ∏ i : Fin 4, a i ^ d i := by
  unfold smithConformalInflateSection
  unfold smithConformalCoefficientFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [mul_pow]

/-! ## Integral normalised Smith transform -/

/-- Coefficientwise integrality condition for the normalised conformal
transform `mu^(-1) P(DY)`.

For every source monomial occurring in `P`, the inflated coefficient is
divisible by the conformal multiplier. -/
def HasIntegralSmithConformalCoefficientDivisibility
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    smithConformalMultiplier (K := K) theta1 theta2 ∣
      smithConformalCoefficientFactor
          (K := K) theta1 theta2 d *
        MvPolynomial.coeff d P

/-- Chosen normalised coefficient. -/
noncomputable def smithConformalCoefficientQuotient
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (d : Fin 4 →₀ ℕ) :
    Polynomial K :=
  if hd : d ∈ P.support then
    Classical.choose (hdiv d hd)
  else
    0

/-- Exact coefficient factorisation on the support. -/
theorem smithConformalCoefficientQuotient_spec_of_mem
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.support) :
    smithConformalCoefficientFactor
        (K := K) theta1 theta2 d *
      MvPolynomial.coeff d P =
        smithConformalMultiplier
            (K := K) theta1 theta2 *
          smithConformalCoefficientQuotient
            theta1 theta2 P hdiv d := by
  unfold smithConformalCoefficientQuotient
  rw [dif_pos hd]
  exact Classical.choose_spec (hdiv d hd)

/-- Explicit integral normalised Smith conformal family. -/
noncomputable def integralSmithConformalFamily
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (smithConformalCoefficientQuotient
        theta1 theta2 P hdiv d)

/-- Evaluation form of the normalised conformal identity

    mu * Q(a) = P(Da).
-/
theorem eval_integralSmithConformalFamily
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (a : Fin 4 → Polynomial K) :
    smithConformalMultiplier (K := K) theta1 theta2 *
        MvPolynomial.eval a
          (integralSmithConformalFamily
            theta1 theta2 P hdiv) =
      MvPolynomial.eval
        (smithConformalInflateSection
          theta1 theta2 a)
        P := by
  classical
  unfold integralSmithConformalFamily
  simp only [MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  rw [MvPolynomial.eval_eq']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finsupp.prod_fintype
    d
    (fun n e => a n ^ e)
    (by
      intro i
      simp)]
  rw [fin4_smithConformalInflateSection_monomialProduct]
  have hq :=
    smithConformalCoefficientQuotient_spec_of_mem
      theta1 theta2 P hdiv hd
  calc
    smithConformalMultiplier (K := K) theta1 theta2 *
        (smithConformalCoefficientQuotient
          theta1 theta2 P hdiv d *
          ∏ i : Fin 4, a i ^ d i) =
      (smithConformalMultiplier (K := K) theta1 theta2 *
        smithConformalCoefficientQuotient
          theta1 theta2 P hdiv d) *
        ∏ i : Fin 4, a i ^ d i := by
          ring
    _ =
      (smithConformalCoefficientFactor
          (K := K) theta1 theta2 d *
        MvPolynomial.coeff d P) *
        ∏ i : Fin 4, a i ^ d i := by
          rw [← hq]
    _ =
      MvPolynomial.coeff d P *
        (smithConformalCoefficientFactor
            (K := K) theta1 theta2 d *
          ∏ i : Fin 4, a i ^ d i) := by
            ring

/-- **Exact polynomial identity for the integral normalised Smith action.**

    Inflate(P) = C(mu) * Q.
-/
theorem smithConformalInflate_integralSmithConformalFamily_eq
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    smithConformalInflateHom (K := K) theta1 theta2 P =
      MvPolynomial.C
          (smithConformalMultiplier
            (K := K) theta1 theta2) *
        integralSmithConformalFamily
          theta1 theta2 P hdiv := by
  apply MvPolynomial.funext
  intro a
  rw [eval_smithConformalInflateHom]
  have h :=
    eval_integralSmithConformalFamily
      theta1 theta2 P hdiv a
  simpa using h.symm

/-! ## Chain rule and determinant covariance -/

/-- First-order chain rule for the two-parameter Smith source inflation. -/
theorem pderiv_smithConformalInflateHom
    (theta1 theta2 : ℕ)
    (i : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv i
        (smithConformalInflateHom
          (K := K) theta1 theta2 P) =
      MvPolynomial.C
          (smithConformalDerivativeCoefficient
            (K := K) theta1 theta2 i) *
        smithConformalInflateHom
          (K := K) theta1 theta2
          (MvPolynomial.pderiv i P) := by
  apply MvPolynomial.induction_on P
  · intro c
    simp [smithConformalInflateHom]
  · intro p q hp hq
    simp [hp, hq, mul_add]
  · intro p n hp
    have hp' :
        MvPolynomial.pderiv i
            (MvPolynomial.bind₁
              (smithConformalInflateVariable
                (K := K) theta1 theta2) p) =
          MvPolynomial.C
              (smithConformalDerivativeCoefficient
                (K := K) theta1 theta2 i) *
            MvPolynomial.bind₁
              (smithConformalInflateVariable
                (K := K) theta1 theta2)
              (MvPolynomial.pderiv i p) := by
      simpa [smithConformalInflateHom] using hp
    by_cases hni : n = i
    · subst n
      simp [smithConformalInflateHom,
        smithConformalInflateVariable, hp']
      ring
    · have hin : i ≠ n := Ne.symm hni
      simp [smithConformalInflateHom,
        smithConformalInflateVariable,
        hp', hni, hin]
      ring

/-- Hessian entry covariance. -/
theorem hessian_smithConformalInflateHom_entry
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (smithConformalInflateHom
          (K := K) theta1 theta2 P) i j =
      MvPolynomial.C
          (smithConformalDerivativeCoefficient
            (K := K) theta1 theta2 i) *
        MvPolynomial.C
          (smithConformalDerivativeCoefficient
            (K := K) theta1 theta2 j) *
        smithConformalInflateHom
          (K := K) theta1 theta2
          (HC4.Polynomial.hessian P i j) := by
  rw [HC4.Polynomial.hessian_apply]
  rw [pderiv_smithConformalInflateHom
    theta1 theta2 i P]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_smithConformalInflateHom
    theta1 theta2 j (MvPolynomial.pderiv i P)]
  rw [HC4.Polynomial.hessian_apply]
  ring

/-- The determinant of the Smith source diagonal is the square of the
conformal multiplier. -/
theorem prod_smithConformalDerivativeCoefficient
    (theta1 theta2 : ℕ) :
    (∏ i : Fin 4,
      (MvPolynomial.C
        (smithConformalDerivativeCoefficient
          (K := K) theta1 theta2 i) :
        MvPolynomial (Fin 4) (Polynomial K))) =
      (MvPolynomial.C
        (smithConformalMultiplier
          (K := K) theta1 theta2) :
        MvPolynomial (Fin 4) (Polynomial K)) ^ 2 := by
  rw [Fin.prod_univ_four]
  simp [smithConformalDerivativeCoefficient,
    smithConformalSourceExponent,
    smithConformalMultiplier,
    smithConformalMultiplierExponent,
    pow_add, pow_two]

/-- Hessian determinant under the honest Smith source inflation. -/
theorem hessianDeterminant_smithConformalInflateHom
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (smithConformalInflateHom
          (K := K) theta1 theta2 P) =
      (MvPolynomial.C
        (smithConformalMultiplier
          (K := K) theta1 theta2)) ^ 4 *
        smithConformalInflateHom
          (K := K) theta1 theta2
          (HC4.Polynomial.hessianDeterminant P) := by
  let v : Fin 4 →
      MvPolynomial (Fin 4) (Polynomial K) :=
    fun i =>
      MvPolynomial.C
        (smithConformalDerivativeCoefficient
          (K := K) theta1 theta2 i)
  let A : Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
    (smithConformalInflateHom
      (K := K) theta1 theta2).mapMatrix
      (HC4.Polynomial.hessian P)
  have hmatrix :
      HC4.Polynomial.hessian
          (smithConformalInflateHom
            (K := K) theta1 theta2 P) =
        fun i j => v i * (v j * A i j) := by
    apply Matrix.ext
    intro i j
    simpa [v, A, mul_assoc] using
      (hessian_smithConformalInflateHom_entry
        (K := K) theta1 theta2 P i j)
  have hv :
      (∏ i : Fin 4, v i) =
        (MvPolynomial.C
          (smithConformalMultiplier
            (K := K) theta1 theta2)) ^ 2 := by
    simpa [v] using
      (prod_smithConformalDerivativeCoefficient
        (K := K) theta1 theta2)
  have hrow :
      (Matrix.det fun i j => v j * A i j) =
        (∏ i : Fin 4, v i) * A.det := by
    exact Matrix.det_mul_row v A
  have hmapdet :
      A.det =
        smithConformalInflateHom
          (K := K) theta1 theta2
          ((HC4.Polynomial.hessian P).det) := by
    simpa [A] using
      (RingHom.map_det
        (smithConformalInflateHom
          (K := K) theta1 theta2)
        (HC4.Polynomial.hessian P)).symm
  unfold HC4.Polynomial.hessianDeterminant
  rw [hmatrix]
  calc
    (Matrix.det fun i j => v i * (v j * A i j)) =
        (∏ i : Fin 4, v i) *
          (Matrix.det fun i j => v j * A i j) := by
      exact Matrix.det_mul_column
        v (fun i j => v j * A i j)
    _ =
        (∏ i : Fin 4, v i) *
          ((∏ i : Fin 4, v i) * A.det) := by
      rw [hrow]
    _ =
        (MvPolynomial.C
          (smithConformalMultiplier
            (K := K) theta1 theta2)) ^ 4 *
          A.det := by
      rw [hv]
      ring
    _ =
        (MvPolynomial.C
          (smithConformalMultiplier
            (K := K) theta1 theta2)) ^ 4 *
          smithConformalInflateHom
            (K := K) theta1 theta2
            ((HC4.Polynomial.hessian P).det) := by
      rw [hmapdet]

/-- Multiplying a four-variable potential by a coefficient-ring scalar
multiplies its Hessian determinant by the fourth power of that scalar. -/
theorem hessianDeterminant_C_mul
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (MvPolynomial.C c * P) =
      (MvPolynomial.C c) ^ 4 *
        HC4.Polynomial.hessianDeterminant P := by
  let v : Fin 4 →
      MvPolynomial (Fin 4) (Polynomial K) :=
    fun _ => MvPolynomial.C c
  let A := HC4.Polynomial.hessian P
  have hmatrix :
      HC4.Polynomial.hessian
          (MvPolynomial.C c * P) =
        fun i j => v i * A i j := by
    apply Matrix.ext
    intro i j
    simp [HC4.Polynomial.hessian_apply,
      MvPolynomial.pderiv_C_mul, v, A]
  have hv :
      (∏ i : Fin 4, v i) =
        (MvPolynomial.C c :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 4 := by
    simp [v, Fin.prod_univ_four, pow_succ]
  unfold HC4.Polynomial.hessianDeterminant
  rw [hmatrix]
  calc
    (Matrix.det fun i j => v i * A i j) =
        (∏ i : Fin 4, v i) * A.det := by
      exact Matrix.det_mul_column v A
    _ =
        (MvPolynomial.C c) ^ 4 * A.det := by
      rw [hv]

/-- **Exact determinant covariance of the integral normalised Smith move.**

The fourth power from the source diagonal is cancelled exactly by the
fourth power of the conformal multiplier. -/
theorem hessianDeterminant_integralSmithConformalFamily
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P) :
    HC4.Polynomial.hessianDeterminant
        (integralSmithConformalFamily
          theta1 theta2 P hdiv) =
      smithConformalInflateHom
        (K := K) theta1 theta2
        (HC4.Polynomial.hessianDeterminant P) := by
  let mu :
      MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C
      (smithConformalMultiplier
        (K := K) theta1 theta2)
  let Q :=
    integralSmithConformalFamily
      theta1 theta2 P hdiv
  have hpoly :=
    smithConformalInflate_integralSmithConformalFamily_eq
      theta1 theta2 P hdiv
  have hdet :=
    congrArg HC4.Polynomial.hessianDeterminant hpoly
  rw [hessianDeterminant_smithConformalInflateHom] at hdet
  rw [hessianDeterminant_C_mul] at hdet
  have hmu :
      mu ≠ 0 := by
    unfold mu
    exact
      MvPolynomial.C_ne_zero.mpr
        (pow_ne_zero
          (smithConformalMultiplierExponent
            theta1 theta2)
          Polynomial.X_ne_zero)
  have hmu4 : mu ^ 4 ≠ 0 :=
    pow_ne_zero 4 hmu
  have hz :
      mu ^ 4 *
        (smithConformalInflateHom
            (K := K) theta1 theta2
            (HC4.Polynomial.hessianDeterminant P) -
          HC4.Polynomial.hessianDeterminant Q) = 0 := by
    dsimp [mu, Q] at hdet ⊢
    rw [mul_sub, hdet, sub_self]
  have hsub :
      smithConformalInflateHom
          (K := K) theta1 theta2
          (HC4.Polynomial.hessianDeterminant P) -
        HC4.Polynomial.hessianDeterminant Q = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hmu4 hzero)
    · exact hzero
  exact (sub_eq_zero.mp hsub).symm

/-- A pure polynomial-family Hessian defect is preserved by the normalised
Smith conformal move. -/
theorem integralSmithConformalFamily_preservesHessianDefect
    (theta1 theta2 Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (integralSmithConformalFamily
        theta1 theta2 P hdiv)
      Delta := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_integralSmithConformalFamily]
  rw [hdef]
  simp [smithConformalInflateHom]

/-! ## Integral marked sections -/

/-- Integrality condition for the inverse source change on a moving marked
section.  It says that each original section coordinate is divisible by the
corresponding Smith diagonal factor. -/
def HasIntegralSmithConformalSectionDivisibility
    (theta1 theta2 : ℕ)
    (a : Fin 4 → Polynomial K) : Prop :=
  ∀ i : Fin 4,
    smithConformalDerivativeCoefficient
        (K := K) theta1 theta2 i ∣
      a i

/-- Chosen transformed marked section. -/
noncomputable def integralSmithConformalSection
    (theta1 theta2 : ℕ)
    (a : Fin 4 → Polynomial K)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        theta1 theta2 a) :
    Fin 4 → Polynomial K :=
  fun i => Classical.choose (hdiv i)

/-- Reinflating the transformed section recovers the original section. -/
theorem smithConformalInflateSection_integralSection_eq
    (theta1 theta2 : ℕ)
    (a : Fin 4 → Polynomial K)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        theta1 theta2 a) :
    smithConformalInflateSection
        theta1 theta2
        (integralSmithConformalSection
          theta1 theta2 a hdiv) =
      a := by
  funext i
  unfold smithConformalInflateSection
  unfold integralSmithConformalSection
  exact (Classical.choose_spec (hdiv i)).symm

/-! ## Exact gradient-collision covariance -/

/-- Derivative evaluation covariance for the integral normalised Smith move.

For the transformed section `a'`:

    mu * d_i Q(a') = D_i * d_i P(a).
-/
theorem eval_pderiv_integralSmithConformalFamily
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hPdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (a : Fin 4 → Polynomial K)
    (hadiv :
      HasIntegralSmithConformalSectionDivisibility
        theta1 theta2 a)
    (i : Fin 4) :
    smithConformalMultiplier (K := K) theta1 theta2 *
      MvPolynomial.eval
        (integralSmithConformalSection
          theta1 theta2 a hadiv)
        (MvPolynomial.pderiv i
          (integralSmithConformalFamily
            theta1 theta2 P hPdiv)) =
      smithConformalDerivativeCoefficient
          (K := K) theta1 theta2 i *
        MvPolynomial.eval a
          (MvPolynomial.pderiv i P) := by
  let a' :=
    integralSmithConformalSection
      theta1 theta2 a hadiv
  have hpoly :=
    smithConformalInflate_integralSmithConformalFamily_eq
      theta1 theta2 P hPdiv
  have hpd :=
    congrArg (MvPolynomial.pderiv i) hpoly
  rw [pderiv_smithConformalInflateHom] at hpd
  rw [MvPolynomial.pderiv_C_mul] at hpd
  have heval :=
    congrArg (MvPolynomial.eval a') hpd
  have hsection :
      smithConformalInflateSection
          theta1 theta2 a' = a := by
    exact
      smithConformalInflateSection_integralSection_eq
        theta1 theta2 a hadiv
  dsimp [a'] at heval ⊢
  simp only [map_mul, MvPolynomial.eval_C] at heval
  rw [eval_smithConformalInflateHom] at heval
  rw [hsection] at heval
  exact heval.symm

/-- **Exact family-gradient collision survives every integral Smith
conformal move.** -/
theorem polynomialFamilyExactGradientCollision_integralSmithConformal
    (theta1 theta2 : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hPdiv :
      HasIntegralSmithConformalCoefficientDivisibility
        theta1 theta2 P)
    (a b : Fin 4 → Polynomial K)
    (hadiv :
      HasIntegralSmithConformalSectionDivisibility
        theta1 theta2 a)
    (hbdiv :
      HasIntegralSmithConformalSectionDivisibility
        theta1 theta2 b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (integralSmithConformalFamily
        theta1 theta2 P hPdiv)
      (integralSmithConformalSection
        theta1 theta2 a hadiv)
      (integralSmithConformalSection
        theta1 theta2 b hbdiv) := by
  intro i
  apply polynomial_X_pow_mul_cancel
    (K := K)
    (smithConformalMultiplierExponent
      theta1 theta2)
  change
    smithConformalMultiplier (K := K) theta1 theta2 *
      MvPolynomial.eval
        (integralSmithConformalSection
          theta1 theta2 a hadiv)
        (MvPolynomial.pderiv i
          (integralSmithConformalFamily
            theta1 theta2 P hPdiv)) =
    smithConformalMultiplier (K := K) theta1 theta2 *
      MvPolynomial.eval
        (integralSmithConformalSection
          theta1 theta2 b hbdiv)
        (MvPolynomial.pderiv i
          (integralSmithConformalFamily
            theta1 theta2 P hPdiv))
  calc
    smithConformalMultiplier (K := K) theta1 theta2 *
        MvPolynomial.eval
          (integralSmithConformalSection
            theta1 theta2 a hadiv)
          (MvPolynomial.pderiv i
            (integralSmithConformalFamily
              theta1 theta2 P hPdiv)) =
      smithConformalDerivativeCoefficient
          (K := K) theta1 theta2 i *
        MvPolynomial.eval a
          (MvPolynomial.pderiv i P) :=
        eval_pderiv_integralSmithConformalFamily
          theta1 theta2 P hPdiv a hadiv i
    _ =
      smithConformalDerivativeCoefficient
          (K := K) theta1 theta2 i *
        MvPolynomial.eval b
          (MvPolynomial.pderiv i P) := by
            rw [hcoll i]
    _ =
      smithConformalMultiplier (K := K) theta1 theta2 *
        MvPolynomial.eval
          (integralSmithConformalSection
            theta1 theta2 b hbdiv)
          (MvPolynomial.pderiv i
            (integralSmithConformalFamily
              theta1 theta2 P hPdiv)) :=
        (eval_pderiv_integralSmithConformalFamily
          theta1 theta2 P hPdiv b hbdiv i).symm

end

end HC4.Valuation
