# Phase 93.30 — close the standard two-zero terminal endpoint under JC2

Built against the clean Phase 93.29.2 tree.

## PlanarJacobianEvaluation

Defines the evaluated planar Jacobian matrix

    J_G(u)[r,c] = eval u (pderiv c (G r))

with rows = output components and columns = input variables.

Kernel-checks

    det J_G(u)
      = eval u (planarJacobianDetPolynomial G).

Thus a `HasNonzeroConstantPlanarJacobian` certificate makes `J_G(u)`
nonsingular at every base point.

## TerminalTwoZeroGradientConjugacy

Defines the standard split

    K^4 -> K^2 × K^2,
    p |-> ((p0,p1),(p2,p3)),

and proves it is injective with inverse `standardJoinPoint`.

For a planarisation

    rename A = pderiv 2 F,
    rename C = pderiv 3 F,

the Phase 93.28 derivative identities are evaluated pointwise.

The positive half of the terminal gradient is exactly

    G(u) = (A(u), C(u)).

The zero-weight half is exactly

    v^T J_G(u).

Hence the actual four-dimensional gradient satisfies the exact conjugacy

    split (grad F p)
      =
    doublingGradientMap
      (eval G) J_G 0 (split p).

## TerminalTwoZeroJC2Endpoint

Combines:

* Phase 93.29 planar Keller reduction;
* the explicit `PlanarJC2Injectivity` hypothesis;
* pointwise nonsingularity of the planar Jacobian matrix;
* the green abstract `doublingGradientMap_injective_of_det_ne_zero`;
* the new exact gradient conjugacy.

The resulting theorem is

    standardTwoZero_terminal_gradient_injective_of_JC2.

It is then lifted to the nonnegative conformal terminal face with standard
zero coordinates `0,1`.

Finally,

    nonnegativeTerminalFace_two_standard_zeros_collision_impossible_of_JC2

states that a distinct exact terminal gradient collision is impossible in
this branch.

If green, this closes the STANDARD k=2 terminal branch completely under
JC2.  A later coordinate-permutation adapter can remove the phrase
"standard coordinates" when assembling the full terminal classification.

No general torus theorem is used.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
