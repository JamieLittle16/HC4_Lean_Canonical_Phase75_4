import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurSpecialKernelLift
import Mathlib.Tactic

/-!
# Constant projective direction of the cleared special Schur kernel

Stage 3 produced, in the honest special-fibre chart, a nonzero polynomial
kernel vector

    D.fullVector : Fin 4 → MvPolynomial (Fin 4) K.

The remaining RS2/Smith theorem is projective: either this polynomial kernel
moves and exposes repair, or all four coordinates share one nonzero polynomial
factor and the residual direction is a constant vector over `K`.

This file packages the latter alternative and proves the denominator
cancellation once and for all.  In particular, if

    D.fullVector i = g * C (v i)

for a nonzero polynomial `g` and a nonzero constant vector `v`, then `v`
itself is an honest kernel direction of the full special-fibre Hessian block.
No localization or division is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- An honest constant source direction in the kernel of the special-fibre
four-block retained by the closing carrier. -/
structure ConstantSpecialSourceKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  direction : Fin 4 → K
  direction_ne_zero : direction ≠ 0
  kernel :
    C.specialFourBlock.matrix.mulVec
      (fun i => MvPolynomial.C (direction i)) = 0

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- The projective-constancy certificate that the remaining Smith/RS2
argument must produce on its null branch.  The full polynomial kernel is a
single nonzero polynomial scalar times a nonzero constant source vector. -/
structure HasConstantProjectiveDirection
    (D : DenominatorClearedSpecialSchurKernelData C) where
  scalar : MvPolynomial (Fin 4) K
  scalar_ne_zero : scalar ≠ 0
  direction : Fin 4 → K
  direction_ne_zero : direction ≠ 0
  factor :
    ∀ i : Fin 4,
      D.fullVector i = scalar * MvPolynomial.C (direction i)

namespace HasConstantProjectiveDirection

variable {D : DenominatorClearedSpecialSchurKernelData C}

/-- The constant polynomial vector associated to the residual source
direction. -/
def constantVector
    (P : D.HasConstantProjectiveDirection) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  fun i => MvPolynomial.C (P.direction i)

/-- The constant polynomial vector is nonzero. -/
theorem constantVector_ne_zero
    (P : D.HasConstantProjectiveDirection) :
    P.constantVector ≠ 0 := by
  intro hzero
  apply P.direction_ne_zero
  funext i
  have hi := congrFun hzero i
  simpa [constantVector] using hi

/-- Matrix multiplication of the factored polynomial kernel is exactly the
same scalar times matrix multiplication of its constant projective part. -/
theorem mulVec_fullVector_eq_scalar_mulVec_constantVector
    (P : D.HasConstantProjectiveDirection) :
    C.specialFourBlock.matrix.mulVec D.fullVector =
      fun i => P.scalar *
        (C.specialFourBlock.matrix.mulVec P.constantVector) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [P.factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [constantVector]
  ac_rfl

/-- Cancel the common nonzero polynomial factor from the full Hessian-kernel
identity.  This is the exact bridge from a constant *projective* Schur/source
kernel to an honest constant source-kernel direction. -/
theorem constantVector_kernel
    (P : D.HasConstantProjectiveDirection) :
    C.specialFourBlock.matrix.mulVec P.constantVector = 0 := by
  funext i
  have hfull := congrFun D.fullVector_kernel i
  have hscale := congrFun P.mulVec_fullVector_eq_scalar_mulVec_constantVector i
  rw [hscale] at hfull
  have hprod :
      P.scalar *
        (C.specialFourBlock.matrix.mulVec P.constantVector) i = 0 := by
    simpa using hfull
  exact (mul_eq_zero.mp hprod).resolve_left P.scalar_ne_zero

/-- Forget the common polynomial factor and retain only the resulting honest
constant source kernel. -/
noncomputable def toConstantSpecialSourceKernelData
    (P : D.HasConstantProjectiveDirection) :
    ConstantSpecialSourceKernelData C where
  direction := P.direction
  direction_ne_zero := P.direction_ne_zero
  kernel := P.constantVector_kernel

end HasConstantProjectiveDirection

end DenominatorClearedSpecialSchurKernelData

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
