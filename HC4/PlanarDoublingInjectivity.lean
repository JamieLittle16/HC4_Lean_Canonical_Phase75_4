import HC4.PlanarJC2Interface
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Abstract Hessian-doubling injectivity

The two-zero-weight terminal endpoint has the standard triangular block
shape

    (u,v) |-> ( J(u)^T v + dD(u),  G(u) ),

where `G : K^2 -> K^2` is the planar Keller map and `J(u)` is its Jacobian
matrix.

This file proves the exact injectivity mechanism independently of any
particular polynomial representation:

* injectivity of `G` recovers `u`;
* invertibility of `J(u)` then recovers `v`.

Thus, once the terminal weighted-support calculation identifies the special
fibre with a Hessian doubling, the only remaining mathematical input is
the planar JC2 injectivity statement.
-/

namespace HC4

noncomputable section

variable {K : Type*} [Field K]

/-- Function-level doubled gradient map.  The first component is the
transpose-Jacobian action `v^T J(u)` plus an arbitrary lower-order
correction depending only on `u`; the second component is the planar map. -/
def doublingGradientMap
    (G : Point2 K -> Point2 K)
    (J : Point2 K -> Matrix (Fin 2) (Fin 2) K)
    (dD : Point2 K -> Point2 K) :
    (Point2 K × Point2 K) ->
      (Point2 K × Point2 K) :=
  fun uv =>
    (fun i =>
      Matrix.vecMul uv.2 (J uv.1) i +
        dD uv.1 i,
     G uv.1)

/-- Abstract doubling injectivity from planar injectivity and fibrewise
injectivity of the Jacobian action. -/
theorem doublingGradientMap_injective
    (G : Point2 K -> Point2 K)
    (J : Point2 K -> Matrix (Fin 2) (Fin 2) K)
    (dD : Point2 K -> Point2 K)
    (hG : Function.Injective G)
    (hJ :
      ∀ u : Point2 K,
        Function.Injective
          (fun v : Point2 K =>
            Matrix.vecMul v (J u))) :
    Function.Injective
      (doublingGradientMap G J dD) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ hEq
  have hGu :
      G u = G u' := by
    exact congrArg Prod.snd hEq
  have huu : u = u' :=
    hG hGu
  subst u'
  have hfirst :
      (fun i =>
        Matrix.vecMul v (J u) i +
          dD u i) =
      (fun i =>
        Matrix.vecMul v' (J u) i +
          dD u i) := by
    exact congrArg Prod.fst hEq
  have hvec :
      Matrix.vecMul v (J u) =
        Matrix.vecMul v' (J u) := by
    funext i
    have hi := congrFun hfirst i
    exact add_right_cancel hi
  have hv : v = v' :=
    hJ u hvec
  subst v'
  rfl

/-- A nonzero determinant makes the row-vector action of a square matrix
injective over a field. -/
theorem vecMul_injective_of_det_ne_zero
    (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : Matrix.det M ≠ 0) :
    Function.Injective
      (fun v : Point2 K =>
        Matrix.vecMul v M) := by
  have hunitDet :
      IsUnit (Matrix.det M) :=
    isUnit_iff_ne_zero.mpr hdet
  have hunitMatrix :
      IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).2 hunitDet
  exact
    Matrix.vecMul_injective_iff_isUnit.mpr
      hunitMatrix

/-- Concrete doubling injectivity from nonzero Jacobian determinants. -/
theorem doublingGradientMap_injective_of_det_ne_zero
    (G : Point2 K -> Point2 K)
    (J : Point2 K -> Matrix (Fin 2) (Fin 2) K)
    (dD : Point2 K -> Point2 K)
    (hG : Function.Injective G)
    (hdet :
      ∀ u : Point2 K,
        Matrix.det (J u) ≠ 0) :
    Function.Injective
      (doublingGradientMap G J dD) := by
  apply
    doublingGradientMap_injective
      G J dD hG
  intro u
  exact
    vecMul_injective_of_det_ne_zero
      (J u) (hdet u)

end

end HC4
