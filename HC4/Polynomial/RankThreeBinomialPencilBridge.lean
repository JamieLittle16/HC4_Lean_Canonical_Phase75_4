import HC4.Polynomial.RankThreeAffineMomentRealisation
import HC4.Polynomial.RankThreeLinearCoefficient
import Mathlib.Tactic

/-!
# A18.5.46: degree-one rank-three edges are literal endpoint pencils

The terminal direction split leaves a special `D = 1` branch.  At degree one
there is no remaining moment ambiguity: if

    phi = c0 + c1 X,

then the line-moment Hessian is exactly

    c0 M(v) + c1 X M(u),

where `v=(0,A,B,C)` and `u=(P,Q,R,S)` are the two endpoint exponents and
`M(z)=z z^T-diag(z)`.

This file records that identity over `Polynomial K`.  It is the missing
bridge between the general affine-line realisation and the already-verified
terminal pencil determinant formulae in `RankThreePencils`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient-weighted polynomial pencil attached to two endpoint
exponents. -/
def weightedRankThreeEndpointPencil
    (A B C P Q R S c0 c1 : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C c0 *
        Polynomial.C (vectorHessianCore ![0, A, B, C] i j) +
      Polynomial.X * Polynomial.C c1 *
        Polynomial.C (vectorHessianCore ![P, Q, R, S] i j)

/-- **Linear coefficient polynomial gives the literal endpoint pencil.** -/
set_option maxHeartbeats 4000000 in
theorem rankThreeAffinePolynomialMomentHessian_linear_eq_endpointPencil
    (A B C P Q R S c0 c1 : K) :
    rankThreeAffinePolynomialMomentHessian
        A B C P (Q - A) (R - B) (S - C)
        (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X) =
      weightedRankThreeEndpointPencil A B C P Q R S c0 c1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankThreeAffinePolynomialMomentHessian,
      lineMomentHessian, eulerDerivative,
      rankThreeLogBaseExponent, rankThreeLogDirection,
      weightedRankThreeEndpointPencil, vectorHessianCore] <;>
    ring

/-- The unweighted endpoint pencil is the existing generic rank-three pencil. -/
theorem weightedRankThreeEndpointPencil_one_one
    (A B C P Q R S : K) :
    weightedRankThreeEndpointPencil A B C P Q R S 1 1 =
      rankThreePencilPolynomial A B C P Q R S := by
  rw [rankThreePencilPolynomial_eq_core]
  ext i j
  simp [weightedRankThreeEndpointPencil]

end

end HC4.Polynomial
