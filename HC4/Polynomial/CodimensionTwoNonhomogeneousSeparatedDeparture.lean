import HC4.Polynomial.CodimensionTwoNonhomogeneousJointDeparture

/-!
# Nonhomogeneous codimension-two separated-departure pencil

The central finite-staircase development introduced the one-parameter Hessian
core

    C M(p,0,0,r) + X (A M(a,0,m,b) + B M(c,n,0,d)).

The original direct expanded determinant calculation in this file has been
superseded by the rooted source-honest route:

* total-deficit reverse Rees;
* exact first positive source layer;
* rank-two second determinant variation;
* binary Hesse rigidity; and
* adjacent-deficit exclusion.

Keeping the pencil definition remains useful for diagnostics and comparison,
but the large unrooted coefficient expansion is deliberately not part of the
live A19 proof path.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- One-parameter Hessian core with two separated first-order departures. -/
noncomputable def codimensionTwoNonhomogeneousSeparatedPencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C C *
        Polynomial.C
          (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      Polynomial.X *
        (Polynomial.C A *
            Polynomial.C
              (vectorHessianCore (K := K) ![a, 0, m, b] i j) +
          Polynomial.C B *
            Polynomial.C
              (vectorHessianCore (K := K) ![c, n, 0, d] i j))

end

end HC4.Polynomial
