# Phase 93.32 — equal-weight linear blocks are injective

Built against the clean Phase 93.31.2 source state.

## TerminalPositiveWeightLinearBlocks

For the determinant-matched permuted gradient

    G_i = pderiv (pi i) F,

define its linear matrix by

    L[j,i] = Hess(F)(0)[j, pi i].

The index orientation is chosen so that `Matrix.vecMul v L` is the linear
part of `G`.

The module proves:

1. `vecMul _ L` is injective because it is the nondegenerate actual
   terminal Hessian followed by an output permutation.

2. If `L[j,i] != 0`, conformality and the matching relation imply

       lambda j = lambda i.

   Therefore cross-weight entries vanish.

3. If a vector is supported on one weight level `t`, and the equations in
   output coordinates of weight `t` vanish, then all output coordinates
   vanish: off-weight coordinates vanish automatically by the block-zero
   pattern.

   Global injectivity of `L` then gives `v = 0`.

This proves every same-weight linear block has trivial kernel without
forming or evaluating any subdeterminants.

The module also identifies `L[j,i]` with the coefficient of `X_j` in the
permuted-gradient component `G_i`, connecting the linear algebra directly
to Phase 93.31's support decomposition.

## TerminalPositiveWeightRecursiveCertificate

Packages, for one determinant matching:

* triangular support from Phase 93.31;
* global injectivity of the linear matrix;
* cross-weight vanishing of that matrix.

The only remaining k=0 theorem is now the finite minimal-weight argument:
given two points with equal permuted gradient, choose the least terminal
weight on which they differ.  Lower-weight nonlinear terms agree, while
the same-weight difference lies in the corresponding linear-block kernel.
Phase 93.32 then forces that difference to vanish, contradiction.

No general torus theorem is used.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
