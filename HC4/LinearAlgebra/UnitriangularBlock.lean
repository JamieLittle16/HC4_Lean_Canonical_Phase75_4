import HC4.MongeAmpere.SchurReduction

/-!
# Unitriangular block Jacobians

After the source and target coordinates of either classified gradient are
ordered by the recovered invariant coordinates, its Jacobian has block form

    [ I  0 ]       or       [ I  D ]
    [ D  I ]                [ 0  I ].

The determinant is one independently of the correction block `D`.  This is
the matrix-level reason the triangular endpoint is étale with unit Jacobian.
-/

namespace HC4.LinearAlgebra

section Blocks

variable {R m n : Type*}
  [CommRing R]
  [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- Lower block-unitriangular matrix with correction block `D`. -/
def lowerBlockUnitriangular (D : Matrix n m R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks 1 0 D 1

/-- Upper block-unitriangular matrix with correction block `D`. -/
def upperBlockUnitriangular (D : Matrix m n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks 1 D 0 1

/-- A lower block-unitriangular matrix has determinant one. -/
theorem det_lowerBlockUnitriangular (D : Matrix n m R) :
    (lowerBlockUnitriangular D).det = 1 := by
  simp [lowerBlockUnitriangular]

/-- An upper block-unitriangular matrix has determinant one. -/
theorem det_upperBlockUnitriangular (D : Matrix m n R) :
    (upperBlockUnitriangular D).det = 1 := by
  simp [upperBlockUnitriangular]

/-- A product of lower and upper block shears still has determinant one. -/
theorem det_lower_mul_upper
    (D : Matrix n m R) (E : Matrix m n R) :
    (lowerBlockUnitriangular D * upperBlockUnitriangular E).det = 1 := by
  rw [Matrix.det_mul, det_lowerBlockUnitriangular, det_upperBlockUnitriangular]
  simp

/-- Pointwise lower-unitriangular matrix fields have constant determinant one. -/
theorem lowerBlockUnitriangular_det_one
    {X : Type*} (D : X → Matrix n m R) :
    ∀ x, (lowerBlockUnitriangular (D x)).det = 1 := by
  intro x
  exact det_lowerBlockUnitriangular (D x)

/-- Pointwise upper-unitriangular matrix fields have constant determinant one. -/
theorem upperBlockUnitriangular_det_one
    {X : Type*} (D : X → Matrix m n R) :
    ∀ x, (upperBlockUnitriangular (D x)).det = 1 := by
  intro x
  exact det_upperBlockUnitriangular (D x)

end Blocks

end HC4.LinearAlgebra
