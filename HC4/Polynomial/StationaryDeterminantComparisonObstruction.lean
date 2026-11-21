import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The stationary Euler rows do not identify the two determinants

These exact rational matrices are the scalar Euler-Hessian cores of the
honest monomial `Q = tau^6 * y^2 * z^3 * w^8`, for `V=2`, `ell=4`,
`n=3`, stationary weight `6`, total degree `12`, and depth `1`.

The source matrix is singular and its active `(2,3)` pivot is nonzero.
It satisfies both falling carrier rows. The canonical parameter/depth
Hessian is nonsingular. Thus a comparison must use more than these rows and
source singularity. This does not instantiate an A19 frontier: its required
locked and highest endpoints are absent.
-/

namespace HC4.Polynomial.StationaryDeterminantComparisonObstruction
open scoped Matrix

def exponent : Fin 4 → ℚ := ![0, 2, 3, 8]
def wall : Fin 4 → ℚ := ![6, 4, 2, 0]
def curve : Fin 4 → ℚ := ![2, 2, 2, -1]

def sourceCore : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
     0, 2, 6, 16;
     0, 6, 6, 24;
     0, 16, 24, 56]

def profileCore : Matrix (Fin 2) (Fin 2) ℚ := !![30, 6; 6, 0]

/-- The displayed source matrix is the falling exponent Hessian. -/
theorem sourceCore_entry (i j : Fin 4) :
    sourceCore i j = exponent i * exponent j -
      (if i = j then exponent i else 0) := by
  fin_cases i <;> fin_cases j <;> norm_num [sourceCore, exponent]

/-- Both affine carrier equations hold. -/
theorem carrier_equations :
    (∑ i : Fin 4, wall i * exponent i) = 14 ∧
    (∑ i : Fin 4, curve i * exponent i) = 2 := by
  norm_num [wall, curve, exponent, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The falling wall Hessian row is satisfied. -/
theorem wall_row (i : Fin 4) :
    (∑ j : Fin 4, sourceCore i j * wall j) =
      (14 - wall i) * exponent i := by
  fin_cases i <;>
    norm_num [sourceCore, wall, exponent, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The falling curve Hessian row is satisfied. -/
theorem curve_row (i : Fin 4) :
    (∑ j : Fin 4, sourceCore i j * curve j) =
      (2 - curve i) * exponent i := by
  fin_cases i <;>
    norm_num [sourceCore, curve, exponent, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Singularity and a nonzero active pivot coexist with nonzero profile
Hessian determinant, even with the corrected falling diagonal. -/
theorem determinant_obstruction :
    sourceCore.det = 0 ∧
    sourceCore 2 2 * sourceCore 3 3 - sourceCore 2 3 * sourceCore 3 2 = -240 ∧
    profileCore.det = -36 := by
  constructor
  · have hrow : ∀ j : Fin 4, sourceCore 0 j = 0 := by
      intro j
      fin_cases j <;> rfl
    rw [Matrix.det_succ_row_zero]
    simp [hrow]
  · change (6 : ℚ) * 56 - 24 * 24 = -240 ∧ profileCore.det = -36
    norm_num [profileCore, Matrix.det_fin_two]

/-- The canonical profile rows and the corrected sheared diagonal all hold. -/
theorem corrected_profile_rows :
    (30 : ℚ) + 6 * 6 = (12 - 1) * 6 ∧
    (6 : ℚ) + 6 * 0 = (12 - 6) * 1 ∧
    (6 : ℚ)^2 * (sourceCore 0 0 + sourceCore 0 1 +
      sourceCore 1 0 + sourceCore 1 1) = 30 + (6 + 1) * 6 := by
  norm_num [sourceCore]

end HC4.Polynomial.StationaryDeterminantComparisonObstruction
