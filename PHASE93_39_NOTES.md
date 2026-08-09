# Phase 93.39 — coordinate-permutation transport

Built against the user's clean Phase 93.38.2 result.

The standard k=1 terminal endpoint is now green.  The next task is to
transport the standard-coordinate terminal endpoints to arbitrary
coordinate placements without repeating their algebra.

## Point relabelling

For a coordinate permutation rho, define

    terminalPermutePoint rho p j = p (rho.symm j).

This is the new-coordinate description of the same old point and is
injective, with inverse given by rho.symm.

## Hessian covariance

Using `MvPolynomial.pderiv_rename` twice, the phase proves

    Hess(rename rho F)
      =
    submatrix rho.symm rho.symm
      (mapMatrix (rename rho) (Hess F)).

This is the exact simultaneous source-coordinate reindexing law.

## Hessian determinant invariance

Two standard Mathlib invariances then compose:

* `Matrix.det_submatrix_equiv_self` removes the simultaneous row/column
  reindexing;
* `RingHom.map_det` moves `rename rho` through the determinant.

Thus

    hessianDeterminant (rename rho F)
      =
    rename rho (hessianDeterminant F).

In particular, determinant one is preserved:

    IsPolynomialMongeAmpere F
      ->
    IsPolynomialMongeAmpere (rename rho F).

## Gradient conjugacy

The phase also proves

    grad(rename rho F)(permutePoint rho p)_j
      =
    grad(F)(p)_(rho.symm j).

Hence the renamed gradient is obtained from the original by bijective
source/output coordinate relabelling.

The endpoint result is

    mvGradientMap_rename_perm_injective_iff

showing exact invariance of gradient injectivity under coordinate
permutation.

This is the main structural adapter required to transport the already-green
standard k=1 and k=2 endpoints to arbitrary zero-coordinate placements.

The next phase should add weighted-homogeneity transport and the finite
terminal zero-pattern standardisation, then invoke the standard endpoint
theorems through this adapter.

No previous theorem is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
