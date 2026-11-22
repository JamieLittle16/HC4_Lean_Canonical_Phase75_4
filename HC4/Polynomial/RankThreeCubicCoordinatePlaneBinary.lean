import HC4.Polynomial.RankThreeCubicBinaryPureCube
import HC4.Polynomial.RankThreeCubicTensorLinearChange
import Mathlib.Tactic

/-!
# Coordinate-plane Hessian cofactor and the binary cubic tangent kernel

For a symmetric ternary cubic tensor D the Hessian at a point
(0,u,v) is the pencil u*D(1,-,-)+v*D(2,-,-).
The principal cofactor adj(H)(0,0) is the determinant of its
2x2 tangential Hessian block.

Because D is symmetric this determinant is precisely the
reduced binary cubic Hessian form whose coefficients are
  a=D(1,1,1), b=D(1,1,2), c=D(1,2,2), d=D(2,2,2).

Consequently vanishing of that cofactor at just the three
tangent-plane points (0,1,0), (0,0,1), (0,1,1) forces a
single fixed nonzero tangent direction that lies in the
kernel of the 2x2 tangential Hessian at *every* plane point.

This is the binary cubic rigidity needed for the exactly-double
source pole once the existing adapted frame is applied.
It does not yet assert a kernel for the *full* 3x3 Hessian.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- In the coordinate plane y₀=0, the normal principal
cofactor of the symmetric cubic Hessian is the reduced
Hessian determinant of the restricted binary cubic. -/
theorem cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
    {K : Type*} [CommRing K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (u v : K) :
    (cubicTensorHessianAt D ![(0 : K), u, v]).adjugate 0 0 =
      binaryCubicReducedHessianDet
        (D 1 1 1) (D 1 1 2) (D 1 2 2) (D 2 2 2) u v := by
  classical
  let H := cubicTensorHessianAt D ![(0 : K), u, v]
  have h11 : H 1 1 = D 1 1 1 * u + D 1 1 2 * v := by
    dsimp [H]
    simp [cubicTensorHessianAt, Fin.sum_univ_three]
    rw [hswap₁ 2 1 1, hswap₂ 1 2 1]
    ring
  have h12 : H 1 2 = D 1 1 2 * u + D 1 2 2 * v := by
    dsimp [H]
    simp [cubicTensorHessianAt, Fin.sum_univ_three]
    rw [hswap₁ 2 1 2]
    ring
  have h21 : H 2 1 = D 1 1 2 * u + D 1 2 2 * v := by
    dsimp [H]
    simp [cubicTensorHessianAt, Fin.sum_univ_three]
    rw [hswap₂ 1 2 1, hswap₂ 2 2 1, hswap₁ 2 1 2]
    ring
  have h22 : H 2 2 = D 1 2 2 * u + D 2 2 2 * v := by
    dsimp [H]
    simp [cubicTensorHessianAt, Fin.sum_univ_three]
    ring
  change H.adjugate 0 0 = _
  have hcof : H.adjugate 0 0 =
      H 1 1 * H 2 2 - H 1 2 * H 2 1 := by
    simp [Matrix.adjugate_fin_three]
  rw [hcof, h11, h12, h21, h22]
  simp only [binaryCubicReducedHessianDet, pow_two]

/-- Three vanishing normal cofactors of the coordinate-plane
cubic Hessian force a fixed nonzero kernel vector for the
binary tangent block along the whole plane. -/
theorem cubicTensor_coordinatePlane_normalCofactor_threeZeros_constantTangentKernel
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (h10 : (cubicTensorHessianAt D ![(0 : K), 1, 0]).adjugate 0 0 = 0)
    (h01 : (cubicTensorHessianAt D ![(0 : K), 0, 1]).adjugate 0 0 = 0)
    (h11 : (cubicTensorHessianAt D ![(0 : K), 1, 1]).adjugate 0 0 = 0) :
    ∃ r t : K,
      (r ≠ 0 ∨ t ≠ 0) ∧
      ∀ u v : K,
        ((D 1 1 1 * u + D 1 1 2 * v) * r +
          (D 1 1 2 * u + D 1 2 2 * v) * t = 0) ∧
        ((D 1 1 2 * u + D 1 2 2 * v) * r +
          (D 1 2 2 * u + D 2 2 2 * v) * t = 0) := by
  apply binaryCubic_reducedHessian_threeZeros_constantKernel
    (D 1 1 1) (D 1 1 2) (D 1 2 2) (D 2 2 2)
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h10
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h01
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h11


/-- The restricted ternary cubic's binary part is a pure cube
whenever the normal principal cofactor vanishes at three plane
points. This is a coefficient classification: the four
coefficients are those of the *same symmetric source tensor*,
not a newly chosen polynomial. -/
theorem cubicTensor_coordinatePlane_normalCofactor_threeZeros_pureCube
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (h10 : (cubicTensorHessianAt D ![(0 : K), 1, 0]).adjugate 0 0 = 0)
    (h01 : (cubicTensorHessianAt D ![(0 : K), 0, 1]).adjugate 0 0 = 0)
    (h11 : (cubicTensorHessianAt D ![(0 : K), 1, 1]).adjugate 0 0 = 0) :
    ((D 1 1 1 = 0 ∧ D 1 1 2 = 0 ∧ D 1 2 2 = 0) ∨
      (D 1 1 1 ≠ 0 ∧
        ∀ u v : K,
          D 1 1 1 * u ^ 3 +
              3 * D 1 1 2 * u ^ 2 * v +
              3 * D 1 2 2 * u * v ^ 2 +
              D 2 2 2 * v ^ 3 =
            D 1 1 1 *
              (u + (D 1 1 2 / D 1 1 1) * v) ^ 3)) := by
  apply binaryCubic_pureCube_of_reducedHessian_threeZeros
    (D 1 1 1) (D 1 1 2) (D 1 2 2) (D 2 2 2)
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h10
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h01
  · simpa only [
      cubicTensor_coordinatePlane_normalCofactor_eq_binaryDet
        D hswap₁ hswap₂] using h11

end
end HC4.Polynomial.RankThreeCubic
