import HC4.Polynomial.CodimensionTwoNonhomogeneousDeparturePencil
import Mathlib.Tactic

/-!
# Nonhomogeneous codimension-two joint-departure pencil

The central finite-staircase analysis introduced the coefficient-weighted
one-parameter Hessian core

    C M(p,0,0,r) + X A M(a,m,n,b).

This definition remains useful as a compact state-free representation of a
joint departure.  The earlier direct determinant-coefficient calculation in
this module is no longer on the live A19 route: the rooted central proof now
passes through the total-deficit first layer, binary Hesse rigidity, and the
adjacent-support obstruction.  Keeping that large expanded polynomial proof
would duplicate the stronger rooted argument and make compilation brittle.

No valuation clock, repair state, or JC2 hypothesis appears here.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Coefficient-weighted one-parameter Hessian core of a positive
codimension-two base monomial and one joint departure. -/
noncomputable def codimensionTwoNonhomogeneousJointPencil
    {K : Type*} [CommRing K]
    (p r a m n b C A : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C C *
        Polynomial.C
          (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      Polynomial.X * Polynomial.C A *
        Polynomial.C
          (vectorHessianCore (K := K) ![a, m, n, b] i j)

end

end HC4.Polynomial
