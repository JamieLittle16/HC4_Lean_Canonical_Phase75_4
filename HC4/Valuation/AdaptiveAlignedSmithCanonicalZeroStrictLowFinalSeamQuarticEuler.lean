import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticParity
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyEulerRadialReduction
import Mathlib.Tactic

/-!
# G25: Euler column identity for the quartic final seam

G24 shows that at the positive midpoint v = (1/2)e0,

    grad(q2)(v) + grad(h4)(v) = 0.

Euler's identity differentiated once says that for a homogeneous degree-m
form H,

    Hess(H)(v) * v = (m - 1) grad(H)(v).

Since v has only coordinate zero nonzero, the G24 collision relation becomes

    Hess(h4)(v)_{i0} + 3 Hess(q2)(v)_{i0} = 0

for every row i.

Thus the quartic Hessian acts on the marked direction by a fixed -3 correction
relative to the nondegenerate quadratic Hessian from G23.

No JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Evaluated differentiated Euler identity for an ordinary homogeneous
polynomial. -/
theorem homogeneous_hessian_eval_radial
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (p : Fin n → K)
    (i : Fin n) :
    (∑ j : Fin n,
      MvPolynomial.eval p (HC4.Polynomial.hessian H i j) * p j) =
      ((m - 1 : ℕ) : K) *
        MvPolynomial.eval p (MvPolynomial.pderiv i H) := by
  have hEuler := homogeneous_hessian_mul_X H m hhom i
  have hEval := congrArg (MvPolynomial.eval p) hEuler
  simpa only [map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    using hEval

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The midpoint quartic Hessian column is exactly -3 times the quadratic
Hessian column in the marked direction. -/
theorem FinalSeamQuarticCoreCollisionData.h4_hessian_column_zero_relation
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticCoreCollisionData)
    (i : Fin 4) :
    MvPolynomial.eval (finalSeamMidpointRight (K := K))
        (HC4.Polynomial.hessian C.homogeneousCore.h4 i (0 : Fin 4)) +
      (3 : K) *
        MvPolynomial.eval (finalSeamMidpointRight (K := K))
          (HC4.Polynomial.hessian C.homogeneousCore.q2 i (0 : Fin 4)) = 0 := by
  let Q := C.homogeneousCore
  let p : Fin 4 → K := finalSeamMidpointRight (K := K)
  let x : K := finalSeamHalf (K := K)

  have hqEulerRaw :=
    homogeneous_hessian_eval_radial
      (K := K) Q.q2 2 Q.q2_homogeneous p i
  have hqEuler :
      MvPolynomial.eval p
          (HC4.Polynomial.hessian Q.q2 i (0 : Fin 4)) * x =
        MvPolynomial.eval p (MvPolynomial.pderiv i Q.q2) := by
    simpa [p, x, finalSeamMidpointRight, Fin.sum_univ_four] using hqEulerRaw

  have h4EulerRaw :=
    homogeneous_hessian_eval_radial
      (K := K) Q.h4 4 Q.h4_homogeneous p i
  have h4Euler :
      MvPolynomial.eval p
          (HC4.Polynomial.hessian Q.h4 i (0 : Fin 4)) * x =
        (3 : K) *
          MvPolynomial.eval p (MvPolynomial.pderiv i Q.h4) := by
    simpa [p, x, finalSeamMidpointRight, Fin.sum_univ_four] using h4EulerRaw

  have hgrad :
      MvPolynomial.eval p (MvPolynomial.pderiv i Q.q2) +
        MvPolynomial.eval p (MvPolynomial.pderiv i Q.h4) = 0 := by
    simpa [p, Q] using C.q2_add_h4_gradient_eval_right_eq_zero i

  have hxrel :
      x *
        (MvPolynomial.eval p
            (HC4.Polynomial.hessian Q.h4 i (0 : Fin 4)) +
          (3 : K) *
            MvPolynomial.eval p
              (HC4.Polynomial.hessian Q.q2 i (0 : Fin 4))) = 0 := by
    linear_combination h4Euler + 3 * hqEuler + 3 * hgrad

  have hx : x ≠ 0 := by
    dsimp [x, finalSeamHalf]
    norm_num
  have hrel :=
    (mul_eq_zero.mp hxrel).resolve_left hx
  simpa [p, Q] using hrel

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
