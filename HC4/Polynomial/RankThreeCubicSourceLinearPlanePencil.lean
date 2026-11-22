import HC4.Polynomial.RankThreeCubicPencilGlobalKernel
import HC4.Polynomial.RankThreeCubicSourceLinearTensorEvaluation
import Mathlib.Tactic

/-!
# An adapted degree-one polynomial Hessian is a binary linear matrix pencil

If every entry of H(y) is homogeneous linear, the adapted plane
matrix
  B(u,v)=Mᵀ H(M(0,u,v)) M
is exactly
  u*B(1,0)+v*B(0,1).

This is a polynomial evaluation identity, valid for any frame M.
The proof uses the already-verified tensor evaluation theorem
for homogeneous linear Hessian entries. It does not assume the
matrix pencil is integrable, symmetric, or invertible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- The restriction of an arbitrary homogeneous-linear 3x3
polynomial matrix to an adapted two-dimensional plane is a
linear pencil in its two plane coordinates. -/
theorem homogeneousLinearHessian_adaptedPlane_isLinearPencil
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (hhom : ∀ i j : Fin 3, (H i j).IsHomogeneous 1)
    (M : Matrix (Fin 3) (Fin 3) K)
    (u v : K) :
    M.transpose *
        H.map (MvPolynomial.aeval (M.mulVec ![(0 : K), u, v])).toRingHom *
        M =
      u • (M.transpose *
        H.map (MvPolynomial.aeval (M.mulVec ![(0 : K), 1, 0])).toRingHom *
        M) +
      v • (M.transpose *
        H.map (MvPolynomial.aeval (M.mulVec ![(0 : K), 0, 1])).toRingHom *
        M) := by
  classical
  let q : B3 K →+* K :=
    (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom
  let D : Fin 3 → Fin 3 → Fin 3 → K :=
    fun t i j => q (pderiv t (H i j))
  have hqC (a : K) : q (MvPolynomial.C a) = algebraMap K K a := by
    change MvPolynomial.aeval
      (fun _ : Fin 3 => (0 : K)) (MvPolynomial.C a) = a
    simp
  have hEval (w : Fin 3 → K) :
      H.map (MvPolynomial.aeval w).toRingHom =
        cubicTensorHessianAt D w :=
    homogeneousLinearHessian_tensor_evaluation H hhom q hqC w
  let e1 : Fin 3 → K := ![(0 : K), 1, 0]
  let e2 : Fin 3 → K := ![(0 : K), 0, 1]
  let w : Fin 3 → K := ![(0 : K), u, v]
  have hbase :
      H.map (MvPolynomial.aeval (M.mulVec w)).toRingHom =
        u • H.map (MvPolynomial.aeval (M.mulVec e1)).toRingHom +
        v • H.map (MvPolynomial.aeval (M.mulVec e2)).toRingHom := by
    rw [hEval (M.mulVec w), hEval (M.mulVec e1), hEval (M.mulVec e2)]
    ext i j
    simp only [cubicTensorHessianAt, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
    simp [Matrix.mulVec, dotProduct, w, e1, e2, Fin.sum_univ_three]
    ring
  change M.transpose *
    H.map (MvPolynomial.aeval (M.mulVec w)).toRingHom * M =
    u • (M.transpose *
      H.map (MvPolynomial.aeval (M.mulVec e1)).toRingHom * M) +
    v • (M.transpose *
      H.map (MvPolynomial.aeval (M.mulVec e2)).toRingHom * M)
  rw [hbase]
  simp only [Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

end
end HC4.Polynomial.RankThreeCubic
