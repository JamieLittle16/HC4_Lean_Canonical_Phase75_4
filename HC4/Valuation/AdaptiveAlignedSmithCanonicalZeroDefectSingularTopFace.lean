import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import HC4.Polynomial.MaximalHessianInitial
import HC4.MongeAmpere.PolynomialInitial
import Mathlib.Tactic

/-!
# A18.5.10: zero-defect nonlinear top faces are Hessian singular

A18.5.7 handles positive raw defect: the actual special fibre already has
zero Hessian determinant.  Raw defect zero is different: the special fibre
has determinant one.  Nevertheless every genuine maximal ordinary component
of degree at least three is Hessian singular.

Indeed, for ordinary weight one and source degree `m`, the Hessian determinant
of the degree-`m` initial form is the determinant component of weight

    4*m - 8.

For `m >= 3` this weight is nonzero, while a determinant-one polynomial has
no nonzero determinant component at any nonzero weight.  The existing maximal
Hessian-initial theorem therefore gives zero Hessian determinant on the top
component.

This file deliberately does not choose a top degree.  It proves the exact
consumer needed once a later support argument supplies an attained maximal
ordinary degree.  Thus no artificial degree-cap equality is assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- At raw defect zero the actual polynomial special fibre has Hessian
determinant exactly one. -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_specialFiber_hessianDeterminant_eq_one
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber s.family) = 1 := by
  rw [hessianDeterminant_polynomialFamilySpecialFiber]
  have hdef := s.hessianDefect
  unfold HasPolynomialFamilyHessianDefect at hdef
  rw [hdef, hzero]
  simp

/-- **Determinant-one top-face singularity.**

If `F` has no ordinary monomial above degree `m`, `m >= 3`, and
`det Hess(F) = 1`, then its exact ordinary degree-`m` component has zero
Hessian determinant.

The theorem does not assume that the component is nonzero; the later finite
support selection will provide that independently. -/
theorem hessianDeterminant_ordinaryInitial_eq_zero_of_mongeAmpere
    (F : MvPolynomial (Fin 4) K)
    (m : ℕ)
    (hm : 3 ≤ m)
    (hLE :
      HC4.Polynomial.IsWeightLE
        (fun _ : Fin 4 => (1 : ℤ)) (m : ℤ) F)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm
        (fun _ : Fin 4 => (1 : ℤ)) (m : ℤ) F) = 0 := by
  rw [← HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    (fun _ : Fin 4 => (1 : ℤ)) (m : ℤ) F hLE]
  apply HC4.MongeAmpere.initialForm_hessianDeterminant_eq_zero hMA
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  norm_num
  omega

/-- State-facing zero-defect form.  Once an attained maximal ordinary degree
`m >= 3` of the terminal special fibre is supplied, the corresponding honest
initial face is singular. -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_ordinaryInitial_hessianDeterminant_eq_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0)
    (m : ℕ)
    (hm : 3 ≤ m)
    (hLE :
      HC4.Polynomial.IsWeightLE
        (fun _ : Fin 4 => (1 : ℤ)) (m : ℤ)
        (polynomialFamilySpecialFiber s.family)) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm
        (fun _ : Fin 4 => (1 : ℤ)) (m : ℤ)
        (polynomialFamilySpecialFiber s.family)) = 0 := by
  apply hessianDeterminant_ordinaryInitial_eq_zero_of_mongeAmpere
    (polynomialFamilySpecialFiber s.family) m hm hLE
  exact s.zeroDefect_specialFiber_hessianDeterminant_eq_one hzero

end

end HC4.Valuation
