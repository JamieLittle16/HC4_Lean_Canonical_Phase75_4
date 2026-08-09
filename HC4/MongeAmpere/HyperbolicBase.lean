import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The hyperbolic base Hessian

The quadratic base potential `Q = x₁x₄ + x₂x₃` has, after pairing the
variables, two hyperbolic `2 × 2` Hessian blocks.  Each block has determinant
`-a²`, so the direct sum of two unit blocks has determinant one.
-/

namespace HC4.MongeAmpere

section Hyperbolic

variable {R : Type*} [CommRing R]

/-- The `2 × 2` hyperbolic Hessian block with mixed entry `a`. -/
def hyperbolicPlane (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, a; a, 0]

/-- Determinant of one hyperbolic plane. -/
theorem det_hyperbolicPlane (a : R) :
    (hyperbolicPlane a).det = -(a ^ 2) := by
  simp [hyperbolicPlane, Matrix.det_fin_two, pow_two]

/-- Direct sum of two hyperbolic planes. -/
def hyperbolicFour (a b : R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks (hyperbolicPlane a) 0 0 (hyperbolicPlane b)

/-- The determinant of two hyperbolic planes is `(a*b)^2`. -/
theorem det_hyperbolicFour (a b : R) :
    (hyperbolicFour a b).det = (a * b) ^ 2 := by
  calc
    (hyperbolicFour a b).det =
        (hyperbolicPlane a).det * (hyperbolicPlane b).det := by
      simp [hyperbolicFour]
    _ = (a * b) ^ 2 := by
      rw [det_hyperbolicPlane, det_hyperbolicPlane]
      ring

/-- The unit hyperbolic four-dimensional Hessian has determinant one. -/
theorem det_hyperbolicFour_one :
    (hyperbolicFour (1 : R) 1).det = 1 := by
  simpa using (det_hyperbolicFour (R := R) (1 : R) 1)

end Hyperbolic

end HC4.MongeAmpere
