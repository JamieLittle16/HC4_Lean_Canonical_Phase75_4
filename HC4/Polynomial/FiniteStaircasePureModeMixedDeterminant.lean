import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# Pure-mode mixed exponent-Hessian determinants

The one-fibre endpoint coupling reduces the two extreme staircase diagonals to
literal translated pure modes.  Their highest longitudinal monomials have
simple exponent vectors, so the first nonzero self-interaction can be read off
from the numerical exponent Hessian core

    M(d) = d d^T - diag(d).

This file records the two exact mixed determinant factorizations needed by the
remaining parameter-order argument.

For the lower extreme `j+2=k`, the locked endpoint leading exponent and the
interior leading exponent are

    (1,0,ell,ell*V),
    (k-1,1,0,V*(k-1)).

For the upper extreme `j=k`, the highest endpoint leading exponent and the
interior leading exponent are

    (1,n-1,0,V*(n-1)),
    (k,0,1,V*k).

No HC4 state, source coefficient, or Rees parameter occurs here.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Field-valued exponent Hessian core for a literal four-tuple. -/
def fieldExponentHessianCore
    {K : Type*} [CommRing K]
    (d : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => d i * d j - if i = j then d i else 0

/-- **Locked/lower pure-mode mixed determinant.**  The quadratic coefficient is
nonzero away from the obvious degenerate integer factors. -/
theorem det_lockedLowerPureMode_pencil
    {K : Type*} [CommRing K]
    (V ell k t : K) :
    (fieldExponentHessianCore ![1, 0, ell, ell * V] +
        t • fieldExponentHessianCore ![k - 1, 1, 0, V * (k - 1)]).det =
      V * (V + 1) * ell * (ell - 1) * (k - 1) ^ 2 * t ^ 2 *
        (ell + (k - 1) * t) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [fieldExponentHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- **Highest/upper pure-mode mixed determinant.**  This is the endpoint-dual
factorization to `det_lockedLowerPureMode_pencil`. -/
theorem det_highestUpperPureMode_pencil
    {K : Type*} [CommRing K]
    (V n k t : K) :
    (fieldExponentHessianCore ![1, n - 1, 0, V * (n - 1)] +
        t • fieldExponentHessianCore ![k, 0, 1, V * k]).det =
      V * (V + 1) * (n - 1) * k ^ 2 * (n - 2) * t ^ 2 *
        ((n - 1) + k * t) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [fieldExponentHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
