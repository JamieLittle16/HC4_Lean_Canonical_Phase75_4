import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur-complement reduction for block Hessians

The partial Legendre-transform step in the HC4 argument repeatedly reduces a
block determinant to the determinant of a Schur complement.  This module
records the exact determinant and invertibility equivalences in a form ready
for pointwise Hessian application.
-/

namespace HC4.MongeAmpere

section Schur

variable {R m n : Type*}
  [CommRing R]
  [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- Schur complement of the top-left block. -/
def schur₁₁
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible A] :
    Matrix n n R :=
  D - C * ⅟ A * B

/-- Schur complement of the bottom-right block. -/
def schur₂₂
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible D] :
    Matrix m m R :=
  A - B * ⅟ D * C

/-- Determinant reduction around an invertible top-left block. -/
theorem det_fromBlocks_schur₁₁
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = A.det * (schur₁₁ A B C D).det := by
  simpa [schur₁₁] using Matrix.det_fromBlocks₁₁ A B C D

/-- Determinant reduction around an invertible bottom-right block. -/
theorem det_fromBlocks_schur₂₂
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible D] :
    (Matrix.fromBlocks A B C D).det = D.det * (schur₂₂ A B C D).det := by
  simpa [schur₂₂] using Matrix.det_fromBlocks₂₂ A B C D

/-- With identity top-left block, the full determinant is the Schur determinant. -/
theorem det_fromBlocks_one₁₁
    (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks (1 : Matrix m m R) B C D).det = (D - C * B).det := by
  simpa using Matrix.det_fromBlocks_one₁₁ B C D

/-- With identity bottom-right block, the full determinant is the complementary Schur determinant. -/
theorem det_fromBlocks_one₂₂
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) :
    (Matrix.fromBlocks A B C (1 : Matrix n n R)).det = (A - B * C).det := by
  simpa using Matrix.det_fromBlocks_one₂₂ A B C

/-- Constant-determinant equation rewritten as a top-left Schur equation. -/
theorem det_eq_iff_schur₁₁
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible A] (c : R) :
    (Matrix.fromBlocks A B C D).det = c ↔
      A.det * (schur₁₁ A B C D).det = c := by
  rw [det_fromBlocks_schur₁₁]

/-- Constant-determinant equation rewritten as a bottom-right Schur equation. -/
theorem det_eq_iff_schur₂₂
    (A : Matrix m m R) (B : Matrix m n R)
    (C : Matrix n m R) (D : Matrix n n R) [Invertible D] (c : R) :
    (Matrix.fromBlocks A B C D).det = c ↔
      D.det * (schur₂₂ A B C D).det = c := by
  rw [det_fromBlocks_schur₂₂]

/-- A block matrix with invertible top-left block is a unit exactly when its Schur complement is. -/
theorem isUnit_fromBlocks_iff_schur₁₁
    {A : Matrix m m R} {B : Matrix m n R}
    {C : Matrix n m R} {D : Matrix n n R} [Invertible A] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (schur₁₁ A B C D) := by
  simpa [schur₁₁] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
      (A := A) (B := B) (C := C) (D := D))

/-- A block matrix with invertible bottom-right block is a unit exactly when its Schur complement is. -/
theorem isUnit_fromBlocks_iff_schur₂₂
    {A : Matrix m m R} {B : Matrix m n R}
    {C : Matrix n m R} {D : Matrix n n R} [Invertible D] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (schur₂₂ A B C D) := by
  simpa [schur₂₂] using
    (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂
      (A := A) (B := B) (C := C) (D := D))

end Schur

end HC4.MongeAmpere
