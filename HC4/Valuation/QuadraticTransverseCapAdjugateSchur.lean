import HC4.Valuation.QuadraticAxisFourBlockRankTwo
import HC4.Newton.GeneralThreeBlockScalarSchur
import Mathlib.Tactic

/-!
# Exact transverse adjugate certificate for a quadratic-cap Schur source

At any longitudinal parameter x, write the transverse 3x3 Hessian as C
and the longitudinal-to-transverse row as v = b'(x).
If det(C)=0 and the full 4x4 Hessian determinant equals one, the concrete
vector w = adj(C)*v satisfies

  C*w = 0,    v·w = -1.

These are polynomial identities over ANY commutative coefficient ring,
including K[x]. No fraction field, rank conclusion, invented source, or
endpoint assumption is involved. Generic rank two and the y-linear
Hessian coefficient will later give the derivative kernel equations.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {R : Type*} [CommRing R]

/-- First coordinate of adj(C) applied to the transverse mixed Hessian
gradient vector, in the stored 3x3 symmetric block order. -/
def quadraticTransverseAdjugateVector0
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) : R :=
  (C.d * C.f - C.e * C.e) * v₀ +
    (C.c * C.e - C.b * C.f) * v₁ +
    (C.b * C.e - C.c * C.d) * v₂

def quadraticTransverseAdjugateVector1
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) : R :=
  (C.c * C.e - C.b * C.f) * v₀ +
    (C.a * C.f - C.c * C.c) * v₁ +
    (C.b * C.c - C.a * C.e) * v₂

def quadraticTransverseAdjugateVector2
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) : R :=
  (C.b * C.e - C.c * C.d) * v₀ +
    (C.b * C.c - C.a * C.e) * v₁ +
    (C.a * C.d - C.b * C.b) * v₂

/-- The explicit adjugate vector lies in the kernel exactly when
the transverse 3x3 determinant vanishes. -/
theorem quadraticTransverseAdjugate_row0
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) :
    C.a * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
      C.b * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
      C.c * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂ =
        C.determinantCore * v₀ := by
  unfold quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
    GeneralThreeBlock.determinantCore
  ring

theorem quadraticTransverseAdjugate_row1
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) :
    C.b * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
      C.d * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
      C.e * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂ =
        C.determinantCore * v₁ := by
  unfold quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
    GeneralThreeBlock.determinantCore
  ring

theorem quadraticTransverseAdjugate_row2
    (C : GeneralThreeBlock R) (v₀ v₁ v₂ : R) :
    C.c * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
      C.e * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
      C.f * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂ =
        C.determinantCore * v₂ := by
  unfold quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
    GeneralThreeBlock.determinantCore
  ring

/-- The *existing* quadratic-axis four-block determinant core is
exactly det(C)*longitudinalHessian minus v·adj(C)v. -/
theorem quadraticAxisFourBlockCore_eq_transverseAdjugateSchur
    (u v₀ v₁ v₂ : R)
    (C : GeneralThreeBlock R) :
    quadraticAxisFourBlockCore u v₀ v₁ v₂
      C.a C.b C.c C.d C.e C.f =
      u * C.determinantCore -
      (v₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
        v₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
        v₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) := by
  unfold quadraticAxisFourBlockCore
    quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
    GeneralThreeBlock.determinantCore
  ring

/-- In the singular transverse-3x3 case, the unit four-block determinant
yields an explicitly unimodular polynomial kernel vector. -/
theorem quadraticTransverse_singularThreeBlock_unimodularKernel
    (u v₀ v₁ v₂ : R)
    (C : GeneralThreeBlock R)
    (hfour :
      quadraticAxisFourBlockCore u v₀ v₁ v₂
        C.a C.b C.c C.d C.e C.f = 1)
    (hthree : C.determinantCore = 0) :
    let w₀ := quadraticTransverseAdjugateVector0 C v₀ v₁ v₂
    let w₁ := quadraticTransverseAdjugateVector1 C v₀ v₁ v₂
    let w₂ := quadraticTransverseAdjugateVector2 C v₀ v₁ v₂
    v₀ * w₀ + v₁ * w₁ + v₂ * w₂ = -1 ∧
    C.a * w₀ + C.b * w₁ + C.c * w₂ = 0 ∧
    C.b * w₀ + C.d * w₁ + C.e * w₂ = 0 ∧
    C.c * w₀ + C.e * w₁ + C.f * w₂ = 0 := by
  dsimp only
  have hschur :=
    quadraticAxisFourBlockCore_eq_transverseAdjugateSchur
      u v₀ v₁ v₂ C
  rw [hfour, hthree] at hschur
  have hpair :
      v₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
        v₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
        v₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂ = -1 := by
    linear_combination hschur
  refine ⟨hpair, ?_, ?_, ?_⟩
  · rw [quadraticTransverseAdjugate_row0, hthree]
    simp
  · rw [quadraticTransverseAdjugate_row1, hthree]
    simp
  · rw [quadraticTransverseAdjugate_row2, hthree]
    simp

end

end HC4.Valuation
