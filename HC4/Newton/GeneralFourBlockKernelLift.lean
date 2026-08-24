import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Denominator-cleared kernel lift for a general 2+2 four-block

For

    H = [ A  B ]
        [ Bᵀ C ]

with `A` the active `2 × 2` block, the cleared Schur block is

    S = det(A) C - Bᵀ adj(A) B.

A binary vector `n = (u,v)` therefore has the polynomial full-kernel lift

    (-adj(A) B n, det(A) n).

Multiplying by the full four-block gives exactly

    (0, 0, S n).

This file records that identity without division and over an arbitrary
commutative ring. It is the source-safe bridge needed to lift the retained
rank-one Schur line back to the honest special-fibre Hessian block.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {R : Type*} [CommRing R]

namespace GeneralFourBlock

/-- Polynomial denominator-cleared lift of a binary Schur vector `(u,v)` to
all four coordinates. The first two coordinates are `-adj(A) B (u,v)` and
the last two are `det(A) * (u,v)`. -/
def clearedKernelLift
    (H : GeneralFourBlock R)
    (u v : R) : Fin 4 → R :=
  ![-(H.d * (H.p * u + H.q * v) - H.b * (H.r * u + H.s * v)),
    -((-H.b) * (H.p * u + H.q * v) + H.a * (H.r * u + H.s * v)),
    H.activeDet * u,
    H.activeDet * v]

/-- The two cleared Schur equations for a binary vector. -/
def IsClearedSchurKernel
    (H : GeneralFourBlock R)
    (u v : R) : Prop :=
  H.schurA * u + H.schurB * v = 0 ∧
    H.schurB * u + H.schurC * v = 0

/-- Exact denominator-cleared block multiplication identity. -/
theorem matrix_mulVec_clearedKernelLift
    (H : GeneralFourBlock R)
    (u v : R) :
    H.matrix.mulVec (H.clearedKernelLift u v) =
      ![0,
        0,
        H.schurA * u + H.schurB * v,
        H.schurB * u + H.schurC * v] := by
  funext i
  fin_cases i <;>
    simp [matrix, clearedKernelLift, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, schurA, schurB, schurC, activeDet] <;>
    ring

/-- A cleared Schur-kernel vector lifts to an actual kernel vector of the full
four-block, still without division. -/
theorem mulVec_clearedKernelLift_eq_zero
    (H : GeneralFourBlock R)
    (u v : R)
    (hker : H.IsClearedSchurKernel u v) :
    H.matrix.mulVec (H.clearedKernelLift u v) = 0 := by
  rw [H.matrix_mulVec_clearedKernelLift u v]
  funext i
  fin_cases i <;> simp [hker.1, hker.2]

end GeneralFourBlock

end

end HC4.Newton
