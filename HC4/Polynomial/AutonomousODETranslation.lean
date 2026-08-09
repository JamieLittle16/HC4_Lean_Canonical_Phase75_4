import HC4.Polynomial.AutonomousODEPolynomialDegree
import Mathlib.Tactic

/-!
# Translation bridge for polynomial autonomous logarithmic ODEs

The pole-order theorem is naturally stated after translating a nonzero root
`alpha` to the origin.  This file proves that translation introduces no new
hypothesis: composition with `X + C alpha` transports the unshifted Euler and
logarithmic ODE exactly to the shifted operators used in Phases 78--79.

For

    T_alpha(p) = p.comp (X + C alpha),

we prove

    shiftedEuler alpha (T_alpha p) = T_alpha (eulerDerivative p)

and the corresponding identity for the cleared logarithmic second derivative.
Consequently a polynomial autonomous ODE at the original coordinate transports
to the shifted polynomial autonomous ODE at the translated root.
-/

namespace HC4.Polynomial

noncomputable section

/-- Translation of the univariate coordinate by `alpha`. -/
def translatePolynomial
    {K : Type*} [CommSemiring K]
    (alpha : K) (p : Polynomial K) : Polynomial K :=
  p.comp (Polynomial.X + Polynomial.C alpha)

/-- Formal differentiation commutes with translation. -/
theorem derivative_translatePolynomial
    {K : Type*} [CommSemiring K]
    (alpha : K) (p : Polynomial K) :
    Polynomial.derivative (translatePolynomial alpha p) =
      translatePolynomial alpha (Polynomial.derivative p) := by
  unfold translatePolynomial
  rw [Polynomial.derivative_comp, Polynomial.derivative_X_add_C]
  simp

/-- The shifted Euler operator is exactly the translation of ordinary Euler
 differentiation. -/
theorem shiftedEuler_translatePolynomial
    {K : Type*} [CommRing K]
    (alpha : K) (p : Polynomial K) :
    shiftedEuler alpha (translatePolynomial alpha p) =
      translatePolynomial alpha (eulerDerivative p) := by
  unfold shiftedEuler eulerDerivative translatePolynomial
  rw [Polynomial.derivative_comp, Polynomial.derivative_X_add_C]
  simp

/-- At zero shift, the shifted Euler operator is the ordinary Euler operator. -/
theorem shiftedEuler_zero
    {K : Type*} [CommRing K]
    (p : Polynomial K) :
    shiftedEuler 0 p = eulerDerivative p := by
  simp [shiftedEuler, eulerDerivative]

/-- Translation also transports the cleared logarithmic `eta` numerator. -/
theorem shiftedEtaNumerator_translatePolynomial
    {K : Type*} [CommRing K]
    (alpha : K) (p : Polynomial K) :
    shiftedEtaNumerator alpha (translatePolynomial alpha p) =
      translatePolynomial alpha (logarithmicEtaNumerator p) := by
  unfold shiftedEtaNumerator logarithmicEtaNumerator
  rw [shiftedEuler_translatePolynomial alpha p]
  rw [shiftedEuler_translatePolynomial alpha (eulerDerivative p)]
  simp [translatePolynomial]

/-- Zero shift identifies the shifted `eta` numerator with the ordinary one. -/
theorem shiftedEtaNumerator_zero
    {K : Type*} [CommRing K]
    (p : Polynomial K) :
    shiftedEtaNumerator 0 p = logarithmicEtaNumerator p := by
  unfold shiftedEtaNumerator logarithmicEtaNumerator
  rw [shiftedEuler_zero p, shiftedEuler_zero (eulerDerivative p)]

/-- Translation transports the denominator-cleared polynomial autonomous
right-hand side term-by-term. -/
theorem shiftedAutonomousClearedRHS_translatePolynomial
    {K : Type*} [CommRing K]
    (alpha : K) (R p : Polynomial K) :
    shiftedAutonomousClearedRHS alpha R (translatePolynomial alpha p) =
      translatePolynomial alpha (shiftedAutonomousClearedRHS 0 R p) := by
  classical
  let s : Polynomial K := Polynomial.X + Polynomial.C alpha
  unfold shiftedAutonomousClearedRHS
  dsimp only
  rw [Polynomial.sum_def, Polynomial.sum_def]
  change
    (∑ j ∈ R.support,
      Polynomial.C (R.coeff j) *
        (shiftedEuler alpha (translatePolynomial alpha p)) ^ j *
        (translatePolynomial alpha p) ^ (R.natDegree - j)) =
      (∑ j ∈ R.support,
        Polynomial.C (R.coeff j) *
          (shiftedEuler 0 p) ^ j * p ^ (R.natDegree - j)).comp s
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [shiftedEuler_translatePolynomial, shiftedEuler_zero]
  simp [translatePolynomial, s]

/-- A polynomial autonomous logarithmic ODE transports exactly under
translation of the independent variable. -/
theorem shiftedPolynomialAutonomousLogODE_translate
    {K : Type*} [CommRing K]
    {alpha : K} {R p : Polynomial K}
    (hode : ShiftedPolynomialAutonomousLogODE 0 R p) :
    ShiftedPolynomialAutonomousLogODE alpha R
      (translatePolynomial alpha p) := by
  unfold ShiftedPolynomialAutonomousLogODE at hode ⊢
  have hode' :
      logarithmicEtaNumerator p * p ^ (R.natDegree - 2) =
        shiftedAutonomousClearedRHS 0 R p := by
    rw [← shiftedEtaNumerator_zero]
    exact hode
  calc
    shiftedEtaNumerator alpha (translatePolynomial alpha p) *
        (translatePolynomial alpha p) ^ (R.natDegree - 2) =
      translatePolynomial alpha (logarithmicEtaNumerator p) *
        (translatePolynomial alpha p) ^ (R.natDegree - 2) := by
          rw [shiftedEtaNumerator_translatePolynomial]
    _ = translatePolynomial alpha
        (logarithmicEtaNumerator p * p ^ (R.natDegree - 2)) := by
          simp [translatePolynomial]
    _ = translatePolynomial alpha (shiftedAutonomousClearedRHS 0 R p) := by
          rw [hode']
    _ = shiftedAutonomousClearedRHS alpha R
        (translatePolynomial alpha p) := by
          symm
          exact shiftedAutonomousClearedRHS_translatePolynomial alpha R p

/-- The Phase-79 degree bound can therefore be applied after translation as
soon as the translated polynomial is presented in its root-multiplicity
factorisation. -/
theorem natDegree_le_two_of_polynomialAutonomousLogODE_after_translation
    {K : Type*} [Field K] [CharZero K]
    {alpha : K} {R p q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0)
    (hq0 : q.coeff 0 ≠ 0)
    (hfactor : translatePolynomial alpha p =
      Polynomial.X ^ (n + 1) * q)
    (hode : ShiftedPolynomialAutonomousLogODE 0 R p) :
    R.natDegree ≤ 2 := by
  have hshift := shiftedPolynomialAutonomousLogODE_translate
    (alpha := alpha) hode
  rw [hfactor] at hshift
  exact natDegree_le_two_of_shiftedPolynomialAutonomousLogODE
    halpha hq0 hshift

end

end HC4.Polynomial
