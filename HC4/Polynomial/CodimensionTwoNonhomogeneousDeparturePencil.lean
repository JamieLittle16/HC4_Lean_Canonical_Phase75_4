import HC4.Polynomial.RankThreePencils

/-!
# Nonhomogeneous codimension-two departure pencil

This module keeps the state-free two-parameter pencil used during exploration
of the central finite-staircase branch.

For exponent vectors

    v = (p, 0, 0, r),
    u = (a, 0, m, b),
    w = (c, n, 0, d),

and honest source coefficients `C,A,B`, the matrix below is

    C M(v) + s A M(u) + t B M(w),

with `M(e) = e e^T - diag(e)`.

The former mixed-coefficient theorem in this file duplicated the later,
strictly cheaper one-parameter joint and separated obstructions and caused a
large nested-`Polynomial` normalization burden.  The live A19 route now uses

* `CodimensionTwoNonhomogeneousJointDeparture`, and
* `CodimensionTwoNonhomogeneousSeparatedDeparture`.

Accordingly this module retains only the reusable pencil definition.  No
mathematical capability on the live proof path is lost.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

private def nestedCnh {K : Type*} [CommRing K]
    (x : K) : Polynomial (Polynomial K) :=
  Polynomial.C (Polynomial.C x)

private def sVarnh {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.X

private def tVarnh {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.C Polynomial.X

/-- Coefficient-weighted two-parameter Hessian core around a possibly
nonhomogeneous codimension-two base monomial.  The `s` departure opens
coordinate `2`, while the `t` departure opens coordinate `1`. -/
noncomputable def codimensionTwoNonhomogeneousDeparturePencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  Matrix.of fun i j =>
    nestedCnh C * nestedCnh
        (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      sVarnh * nestedCnh A * nestedCnh
        (vectorHessianCore (K := K) ![a, 0, m, b] i j) +
      tVarnh * nestedCnh B * nestedCnh
        (vectorHessianCore (K := K) ![c, n, 0, d] i j)

end

end HC4.Polynomial
