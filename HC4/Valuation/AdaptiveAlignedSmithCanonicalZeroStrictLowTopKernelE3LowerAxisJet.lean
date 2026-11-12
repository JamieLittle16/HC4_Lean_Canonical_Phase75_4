import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3TransverseAxisInvisibility
import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import Mathlib.Tactic

/-!
# The first nonlinear E3 face is invisible to the axis Hessian and collision

Let F be the unchanged determinant-one represented source, L its
first actual marked-axis lower transverse face, and R = F - L.

The E3 transverse bound r >= 3 means every entry of Hess(L) restricts
to zero on the entire longitudinal coordinate-0 axis.  Consequently
the axis Hessian matrix of R is exactly that of F and has determinant
one, although Hess(R) need *not* have constant determinant one off-axis.

The first actual layer L also inherits the exact marked-gradient
collision.  Subtracting it from F therefore preserves the collision
at the same two distinct axis points.

This is a genuine low-axis-jet separation, not a claimed repair restart:
off-axis determinant coefficients still couple L and R, and they
are the remaining source of nonlinear E3 constraints.
-/

namespace HC4.Valuation
noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Removing the first nonlinear transverse face from the source changes
no Hessian matrix entry after restricting to the longitudinal axis. -/
theorem PureLongitudinalMarkedE3Data.removeFirstFace_axisHessian_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    (longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
      (HC4.Polynomial.hessian
        (T.topKernelReesSource -
          familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder)) =
    (longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
      (HC4.Polynomial.hessian T.topKernelReesSource) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsub :
      HC4.Polynomial.hessian
        (T.topKernelReesSource -
          familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) i j =
        HC4.Polynomial.hessian T.topKernelReesSource i j -
          HC4.Polynomial.hessian
            (familyParameterLayer
              T.topKernelMarkedAxisFirstContactFamily
              T.topKernelMarkedAxisFirstActualLayerOrder) i j := by
    simp [HC4.Polynomial.hessian_apply]
  rw [hsub, map_sub]
  have hz :=
    D.firstActualHessian_axisRestriction_zero P i j
  simp only [longitudinalAxisRestrictionRingHom_apply]
  rw [hz]
  simp

/-- The lower-axis-jet source remainder has an exactly determinant-one
Hessian *when restricted to the longitudinal axis*.  No global
determinant-one statement is made for the remainder. -/
theorem PureLongitudinalMarkedE3Data.removeFirstFace_axisHessian_det_one
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    ((longitudinalAxisRestrictionRingHom (K := K)).mapMatrix
      (HC4.Polynomial.hessian
        (T.topKernelReesSource -
          familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder))).det = 1 := by
  rw [D.removeFirstFace_axisHessian_eq P]
  let phi := longitudinalAxisRestrictionRingHom (K := K)
  let H := HC4.Polynomial.hessian T.topKernelReesSource
  have hmap : phi H.det = (phi.mapMatrix H).det := phi.map_det H
  calc
    (phi.mapMatrix H).det = phi H.det := hmap.symm
    _ = phi (HC4.Polynomial.hessianDeterminant T.topKernelReesSource) := by rfl
    _ = phi 1 := by rw [T.topKernelReesSource_hessianDeterminant_eq_one]
    _ = 1 := map_one phi

/-- The same remainder still has the original two distinct marked
gradient-collision points.  This does not imply the remainder has
determinant-one Hessian away from the axis. -/
theorem PureLongitudinalMarkedE3Data.removeFirstFace_exactCollision
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    HC4.Newton.HasExactGradientCollision
      (T.topKernelReesSource -
        familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have hF := T.topKernelReesSource_exactCollision
  have hL :=
    P.pureLongitudinal_firstActualLayer_exactCollision
      D.coefficient_ne_zero D.topFace_eq
  intro i
  have hFi := hF i
  have hLi := hL i
  unfold HC4.Newton.mvGradientComponentAt at hFi hLi ⊢
  simp only [MvPolynomial.pderiv_sub, map_sub]
  rw [hFi, hLi]

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
end
end HC4.Valuation
