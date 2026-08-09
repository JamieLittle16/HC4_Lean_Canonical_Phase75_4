import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant transport under Hessian congruence

Under a linear change of coordinates with matrix `P`, a Hessian transforms by
congruence:

    H ↦ Pᵀ H P.

Its determinant is multiplied by `(det P)^2`.  This module packages that
identity pointwise and for matrix-valued fields, including the determinant-one
Monge--Ampère condition.
-/

namespace HC4.LinearAlgebra

section Congruence

variable {R ι X : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Matrix congruence `H ↦ Pᵀ H P`. -/
def congruence (P H : Matrix ι ι R) : Matrix ι ι R :=
  P.transpose * H * P

/-- Determinant of a congruence transform. -/
theorem det_congruence (P H : Matrix ι ι R) :
    (congruence P H).det = P.det ^ 2 * H.det := by
  calc
    (congruence P H).det = P.transpose.det * H.det * P.det := by
      simp [congruence, Matrix.det_mul]
    _ = P.det * H.det * P.det := by rw [Matrix.det_transpose]
    _ = P.det ^ 2 * H.det := by ring

/-- A matrix with determinant square one preserves determinants by congruence. -/
theorem det_congruence_of_det_sq_eq_one
    (P H : Matrix ι ι R) (hP : P.det ^ 2 = 1) :
    (congruence P H).det = H.det := by
  rw [det_congruence, hP, one_mul]

/-- Determinant-one coordinate changes preserve determinants by congruence. -/
theorem det_congruence_of_det_eq_one
    (P H : Matrix ι ι R) (hP : P.det = 1) :
    (congruence P H).det = H.det := by
  apply det_congruence_of_det_sq_eq_one P H
  simp [hP]

/-- Determinant-minus-one coordinate changes also preserve determinants. -/
theorem det_congruence_of_det_eq_neg_one
    (P H : Matrix ι ι R) (hP : P.det = -1) :
    (congruence P H).det = H.det := by
  apply det_congruence_of_det_sq_eq_one P H
  simp [hP]

/-- Pull back a matrix-valued field by a point map and a fixed congruence. -/
def pullbackField
    (P : Matrix ι ι R) (φ : X → X) (H : X → Matrix ι ι R) :
    X → Matrix ι ι R :=
  fun x => congruence P (H (φ x))

/-- A matrix-valued field has constant determinant `c`. -/
def HasConstantDet (H : X → Matrix ι ι R) (c : R) : Prop :=
  ∀ x, (H x).det = c

/-- Determinant transport for a pulled-back matrix field. -/
theorem hasConstantDet_pullback
    (P : Matrix ι ι R) (φ : X → X) (H : X → Matrix ι ι R) (c : R)
    (hH : HasConstantDet H c) :
    HasConstantDet (pullbackField P φ H) (P.det ^ 2 * c) := by
  intro x
  change (congruence P (H (φ x))).det = P.det ^ 2 * c
  rw [det_congruence, hH (φ x)]

/-- If `(det P)^2 = 1`, a constant determinant is unchanged by pullback. -/
theorem hasConstantDet_pullback_of_det_sq_eq_one
    (P : Matrix ι ι R) (φ : X → X) (H : X → Matrix ι ι R) (c : R)
    (hP : P.det ^ 2 = 1) (hH : HasConstantDet H c) :
    HasConstantDet (pullbackField P φ H) c := by
  intro x
  change (congruence P (H (φ x))).det = c
  rw [det_congruence, hP, one_mul, hH (φ x)]

/-- Abstract determinant-one Monge--Ampère condition for a Hessian field. -/
def IsMongeAmpere (H : X → Matrix ι ι R) : Prop :=
  HasConstantDet H 1

/-- Unimodular congruence pullback preserves the Monge--Ampère condition. -/
theorem isMongeAmpere_pullback
    (P : Matrix ι ι R) (φ : X → X) (H : X → Matrix ι ι R)
    (hP : P.det ^ 2 = 1) (hH : IsMongeAmpere H) :
    IsMongeAmpere (pullbackField P φ H) :=
  hasConstantDet_pullback_of_det_sq_eq_one P φ H 1 hP hH

end Congruence

end HC4.LinearAlgebra
