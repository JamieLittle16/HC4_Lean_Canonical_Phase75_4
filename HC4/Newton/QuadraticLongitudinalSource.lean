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

private theorem pderiv_numeral {d n : ℕ} [Nat.AtLeastTwo n] (i : Fin d) :
    pderiv i (ofNat(n) : MvPolynomial (Fin d) K) = 0 :=
  (pderiv i).map_natCast n

private theorem finSuccEquiv_four_X (i : Fin 4) :
    finSuccEquiv K 3 (X i) =
      ![Polynomial.X, Polynomial.C (X 0), Polynomial.C (X 1), Polynomial.C (X 2)] i := by
  fin_cases i
  · exact finSuccEquiv_X_zero
  · exact finSuccEquiv_X_succ (j := 0)
  · exact finSuccEquiv_X_succ (j := 1)
  · exact finSuccEquiv_X_succ (j := 2)

private theorem finSuccEquiv_four_C (c : K) :
    finSuccEquiv K 3 (C c) = Polynomial.C (C c) := by
  simp [finSuccEquiv_apply]

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
      simp [quadraticLongitudinalSourceLift] <;> ring

private theorem finSuccEquiv_quadraticLongitudinalSourceLift
    (f : MvPolynomial (Fin 3) K) :
    finSuccEquiv K 3 (quadraticLongitudinalSourceLift f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [quadraticLongitudinalSourceLift, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp]
    fin_cases j <;> simp [quadraticLongitudinalSourceLift, finSuccEquiv_four_X]

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
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, HC4.Polynomial.hessian_apply,
      quadraticLongitudinalSource, pderiv_numeral,
      pderiv_quadraticLongitudinalSourceLift,
      finSuccEquiv_quadraticLongitudinalSourceLift,
      quadraticLongitudinalHessianBoundary, GeneralFourBlock.matrix,
      finSuccEquiv_four_X, finSuccEquiv_four_C, map_ofNat, pderiv_comm_backport] <;> ring

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
    simp [Polynomial.coeff_one]
  have hk := quadraticLongitudinalHessianBoundary_kernel_coefficient_eq_zero
    (C b) (C g) (C k) (X 0) (X 1) (X 2) (fun i => pderiv i B)
    (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)
    (by simpa using hb) hzero
  simpa using hk


private theorem quadraticLongitudinalSource_factor_ne_zero
    [CharZero K] (b g : K) (hb : b ≠ 0) :
    (3 * C b * X (1 : Fin 3) * X 2 - C g : MvPolynomial (Fin 3) K) ≠ 0 := by
  intro hz
  have hg : g = 0 := by
    have h := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : K))) hz
    simpa using h
  have hzero : 3*b = 0 := by
    have h := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (1 : K))) hz
    simpa [hg] using h
  exact (mul_ne_zero (by norm_num) hb) hzero

/-- Determinant one gives the second kernel derivative equation for the
actual lower source polynomial, with no assumptions on its degree. -/
theorem quadraticLongitudinalSource_kernel_second_derivative_eq_zero
    [CharZero K] (b g k : K) (B D : MvPolynomial (Fin 3) K) (hb : b ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant
      (quadraticLongitudinalSource b g k B D) = 1) :
    pderiv 0 (pderiv 0 B) = 0 := by
  have hk := quadraticLongitudinalSource_kernel_coefficient_eq_zero b g k B D hb hdet
  subst k
  have hzero :
      (quadraticLongitudinalHessianBoundary (C b) (C g) (C (0 : K))
        (X 0) (X 1) (X 2) (fun i => pderiv i B)
        (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)).determinantCore.coeff 5 = 0 := by
    rw [← hessianDeterminant_quadraticLongitudinalSource, hdet, map_one]
    simp [Polynomial.coeff_one]
  simp only [map_zero] at hzero
  exact quadraticLongitudinalHessianBoundary_kernel_second_derivative_eq_zero
    (C b) (C g) (X 0) (X 1) (X 2) (fun i => pderiv i B)
    (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)
    (by simpa using hb) (quadraticLongitudinalSource_factor_ne_zero b g hb) hzero


/-- The same source is quadratic in the kernel coordinate as well: the
third derivative of the longitudinal-constant part vanishes. -/
theorem quadraticLongitudinalSource_kernel_third_derivative_eq_zero
    [CharZero K] (b g k : K) (B D : MvPolynomial (Fin 3) K) (hb : b ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant
      (quadraticLongitudinalSource b g k B D) = 1) :
    pderiv 0 (pderiv 0 (pderiv 0 D)) = 0 := by
  have hk := quadraticLongitudinalSource_kernel_coefficient_eq_zero b g k B D hb hdet
  have hB := quadraticLongitudinalSource_kernel_second_derivative_eq_zero b g k B D hb hdet
  subst k
  have hJ (i : Fin 3) : pderiv 0 (pderiv i (pderiv 0 B)) = 0 := by
    rw [pderiv_comm_backport 0 i, hB, map_zero]
  have hzero :
      (quadraticLongitudinalHessianBoundary (C b) (C g) (C (0 : K))
        (X 0) (X 1) (X 2) (fun i => pderiv i B)
        (HC4.Polynomial.hessian B) (HC4.Polynomial.hessian D)).determinantCore.coeff 4 = 0 := by
    rw [← hessianDeterminant_quadraticLongitudinalSource, hdet, map_one]
    simp [Polynomial.coeff_one]
  simp only [map_zero] at hzero
  rw [quadraticLongitudinalHessianBoundary_coeff_four _ _ _ _ _ _ _ _ hB] at hzero
  have hd := congrArg (pderiv (0 : Fin 3)) hzero
  have hproduct :
      (2 * (C b)^2 * (3*C b*X 1*X 2-C g)) *
        pderiv 0 (pderiv 0 (pderiv 0 D)) = 0 := by
    simpa [pderiv_mul, pderiv_pow, pderiv_numeral, HC4.Polynomial.hessian_apply, hJ, hB] using hd
  have hleft : (2 * (C b)^2 * (3*C b*X 1*X 2-C g) : MvPolynomial (Fin 3) K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by simpa using hb)))
      (quadraticLongitudinalSource_factor_ne_zero b g hb)
  exact (mul_eq_zero.mp hproduct).resolve_left hleft

end
end HC4.Newton
