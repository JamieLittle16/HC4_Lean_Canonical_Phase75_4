import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# The mixed quadratic longitudinal boundary

These are exact Hessian-jet identities for
`F = (b*z*w + g + k*y)*x^2 + B(y,z,w)*x + C(y,z,w)`.
The vectors `v` and matrices `J`, `K` retain the first derivatives of `B`
and the second derivatives of `B`, `C`, in coordinate order `(y,z,w)`.
All lower jets are arbitrary. In particular no common-product assumption is
made about `B` or `C`.

The degree-six coefficient forces `k=0` when `b` is nonzero. The degree-five
coefficient then forces `B_yy=0`, provided `3*b*z*w-g` is nonzero. The
degree-four coefficient records the remaining coupling to `C_yy` exactly.

These identities are conditional finite-jet consumers, not a reduction of
arbitrary presented terminals to quadratic longitudinal degree.
-/

namespace HC4.Newton
noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- The full Hessian jet of a source quadratic in the longitudinal variable. -/
def quadraticLongitudinalHessianBoundary
    (b g k y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) : GeneralFourBlock (Polynomial R) where
  a := C (2 * (b*z*w + g + k*y))
  b := C (2*k)*X + C (v 0)
  p := C (2*b*w)*X + C (v 1)
  q := C (2*b*z)*X + C (v 2)
  d := C (J 0 0)*X + C (K 0 0)
  r := C (J 0 1)*X + C (K 0 1)
  s := C (J 0 2)*X + C (K 0 2)
  x := C (J 1 1)*X + C (K 1 1)
  y := C b*X^2 + C (J 1 2)*X + C (K 1 2)
  z := C (J 2 2)*X + C (K 2 2)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- No lower source jet contributes to the degree-six coefficient. -/
theorem quadraticLongitudinalHessianBoundary_coeff_six
    (b g k y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) :
    (quadraticLongitudinalHessianBoundary b g k y z w v J K).determinantCore.coeff 6 =
      4*b^2*k^2 := by
  simp only [quadraticLongitudinalHessianBoundary, GeneralFourBlock.determinantCore]
  ring_nf
  simp [coeff_add, coeff_mul_C, coeff_C_mul, ← C_pow]
  <;> ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- After the first elimination, the next coefficient detects the genuine
second kernel derivative of the longitudinal-linear source coefficient. -/
theorem quadraticLongitudinalHessianBoundary_coeff_five
    (b g y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) :
    (quadraticLongitudinalHessianBoundary b g 0 y z w v J K).determinantCore.coeff 5 =
      2*b^2*(3*b*z*w-g)*(J 0 0) := by
  simp only [quadraticLongitudinalHessianBoundary, GeneralFourBlock.determinantCore]
  ring_nf
  simp [coeff_add, coeff_mul_C, coeff_C_mul, ← C_pow]
  <;> ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- The remaining degree-four equation, retaining every mixed correction. -/
theorem quadraticLongitudinalHessianBoundary_coeff_four
    (b g y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) (hJ : J 0 0 = 0) :
    (quadraticLongitudinalHessianBoundary b g 0 y z w v J K).determinantCore.coeff 4 =
      2*b^2*(3*b*z*w-g)*(K 0 0) +
        b*(4*b*w^2*(J 0 2)^2 - 4*b*w*z*(J 0 2)*(J 0 1) -
          4*b*w*(v 0)*(J 0 2) + 4*b*z^2*(J 0 1)^2 -
          4*b*z*(v 0)*(J 0 1) + b*(v 0)^2 + 4*g*(J 0 2)*(J 0 1)) := by
  simp only [quadraticLongitudinalHessianBoundary, GeneralFourBlock.determinantCore, hJ]
  ring_nf
  simp [coeff_add, coeff_mul_C, coeff_C_mul, ← C_pow]
  <;> ring

/-- In characteristic zero a nonzero mixed coefficient eliminates the
kernel-linear part of the quadratic longitudinal coefficient. -/
theorem quadraticLongitudinalHessianBoundary_kernel_coefficient_eq_zero
    [IsDomain R] [CharZero R]
    (b g k y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) (hb : b ≠ 0)
    (hzero :
      (quadraticLongitudinalHessianBoundary b g k y z w v J K).determinantCore.coeff 6 = 0) :
    k = 0 := by
  rw [quadraticLongitudinalHessianBoundary_coeff_six] at hzero
  have hb2 : 4*b^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  exact pow_eq_zero ((mul_eq_zero.mp hzero).resolve_left hb2)

/-- The next equation forces the longitudinal-linear coefficient to have
zero second kernel derivative; all later source jets remain unrestricted. -/
theorem quadraticLongitudinalHessianBoundary_kernel_second_derivative_eq_zero
    [IsDomain R] [CharZero R]
    (b g y z w : R) (v : Fin 3 → R)
    (J K : Matrix (Fin 3) (Fin 3) R) (hb : b ≠ 0)
    (hfactor : 3*b*z*w-g ≠ 0)
    (hzero :
      (quadraticLongitudinalHessianBoundary b g 0 y z w v J K).determinantCore.coeff 5 = 0) :
    J 0 0 = 0 := by
  rw [quadraticLongitudinalHessianBoundary_coeff_five] at hzero
  have hleft : 2*b^2*(3*b*z*w-g) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)) hfactor
  exact (mul_eq_zero.mp hzero).resolve_left hleft

end
end HC4.Newton
