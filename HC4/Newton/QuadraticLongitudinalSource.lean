import HC4.Newton.QuadraticLongitudinalHessianBoundary
import HC4.Newton.CharZeroHessianKernelRigidity
import HC4.Polynomial.HessianDeterminant
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Actual polynomial source for the mixed quadratic boundary

The lower source polynomials are arbitrary polynomials in `(y,z,w)`.
This module identifies the actual four-variable Hessian, after the standard
`finSuccEquiv` longitudinal extraction, with the full jet block. It derives
the first kernel coefficient elimination from Hessian determinant one.
No arbitrary terminal is assumed to have this quadratic source form.
-/

namespace HC4.Newton
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K]

/-- Include the three transverse variables as coordinates 1, 2, 3. -/
def quadraticLongitudinalSourceLift :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.aeval ![X 1, X 2, X 3]

private theorem pderiv_quadraticLongitudinalSourceLift
    (f : MvPolynomial (Fin 3) K) (i : Fin 4) :
    pderiv i (quadraticLongitudinalSourceLift f) =
      ![0, quadraticLongitudinalSourceLift (pderiv 0 f),
        quadraticLongitudinalSourceLift (pderiv 1 f),
        quadraticLongitudinalSourceLift (pderiv 2 f)] i := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => fin_cases i <;> simp [quadraticLongitudinalSourceLift]
  | add p q hp hq =>
    fin_cases i <;> simp_all [map_add]
  | mul_X p j hp =>
    rw [map_mul, pderiv_mul, hp]
    fin_cases i <;> fin_cases j <;>
      simp [quadraticLongitudinalSourceLift, pderiv_mul] <;> ring

private theorem finSuccEquiv_quadraticLongitudinalSourceLift
    (f : MvPolynomial (Fin 3) K) :
    finSuccEquiv K 3 (quadraticLongitudinalSourceLift f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [quadraticLongitudinalSourceLift, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp]
    fin_cases j <;> simp [quadraticLongitudinalSourceLift, finSuccEquiv_apply]

/-- A source with a mixed quadratic longitudinal coefficient and completely
unrestricted lower transverse polynomials. -/
def quadraticLongitudinalSource (b g k : K) (B D : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K :=
  (C b * X 2 * X 3 + C g + C k * X 1) * X 0 ^ 2 +
    quadraticLongitudinalSourceLift B * X 0 + quadraticLongitudinalSourceLift D

set_option maxHeartbeats 800000 in
/-- Exact identification of the actual Hessian, including every lower jet. -/
theorem hessian_quadraticLongitudinalSource
    (b g k : K) (B D : MvPolynomial (Fin 3) K) :
    (HC4.Polynomial.hessian (quadraticLongitudinalSource b g k B D)).map
        (finSuccEquiv K 3) =
      (quadraticLongitudinalHessianBoundary (C b) (C g) (C k)
        (X 0) (X 1) (X 2) (fun i => pderiv i B)
        (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)).matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, HC4.Polynomial.hessian_apply,
      quadraticLongitudinalSource, pderiv_pow, pderiv_mul,
      pderiv_quadraticLongitudinalSourceLift,
      finSuccEquiv_quadraticLongitudinalSourceLift,
      quadraticLongitudinalHessianBoundary, GeneralFourBlock.matrix,
      finSuccEquiv_apply, pderiv_comm_backport] <;> ring

/-- Determinant transport uses the actual Hessian and the standard ring
equivalence; there is no potential-identification hypothesis. -/
theorem hessianDeterminant_quadraticLongitudinalSource
    (b g k : K) (B D : MvPolynomial (Fin 3) K) :
    finSuccEquiv K 3
        (HC4.Polynomial.hessianDeterminant (quadraticLongitudinalSource b g k B D)) =
      (quadraticLongitudinalHessianBoundary (C b) (C g) (C k)
        (X 0) (X 1) (X 2) (fun i => pderiv i B)
        (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)).determinantCore := by
  unfold HC4.Polynomial.hessianDeterminant
  calc
    _ = ((HC4.Polynomial.hessian (quadraticLongitudinalSource b g k B D)).map
        (finSuccEquiv K 3)).det :=
      (finSuccEquiv K 3).toRingEquiv.toRingHom.map_det _
    _ = _ := by
      rw [hessian_quadraticLongitudinalSource, GeneralFourBlock.matrix_det]

/-- Source-level elimination of the kernel-linear quadratic coefficient. -/
theorem quadraticLongitudinalSource_kernel_coefficient_eq_zero
    [CharZero K] (b g k : K) (B D : MvPolynomial (Fin 3) K) (hb : b ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant
      (quadraticLongitudinalSource b g k B D) = 1) : k = 0 := by
  have hzero :
      (quadraticLongitudinalHessianBoundary (C b) (C g) (C k)
        (X 0) (X 1) (X 2) (fun i => pderiv i B)
        (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)).determinantCore.coeff 6 = 0 := by
    rw [← hessianDeterminant_quadraticLongitudinalSource, hdet, map_one]
    simp
  have hk := quadraticLongitudinalHessianBoundary_kernel_coefficient_eq_zero
    (C b) (C g) (C k) (X 0) (X 1) (X 2) (fun i => pderiv i B)
    (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)
    (by simpa using hb) hzero
  simpa using hk

end
end HC4.Newton
