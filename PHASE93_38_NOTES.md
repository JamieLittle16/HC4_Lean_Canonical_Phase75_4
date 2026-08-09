# Phase 93.38 — standard one-zero terminal endpoint

Built against the user's clean Phase 93.37 result.

## Evaluation bridge

For

    oneZeroFibreSpecialise c P

the phase proves

    eval u (oneZeroFibreSpecialise c P)
      =
    eval (c,0,u0,u1) P.

The proof uses Mathlib's algebra-hom universal-property lemmas:

    MvPolynomial.comp_aeval_apply
    MvPolynomial.aeval_rename
    MvPolynomial.aeval_eq_eval

and then checks the four coordinates of `oneZeroSplitIndex`.

## Fibre-gradient / ambient-gradient identification

Combining that evaluation theorem with the already-green derivative
specialisation lemmas from Phase 93.36 gives

    fibreGradient(c,F,u)_0 = ambientGradient(F,(c,0,u0,u1))_2
    fibreGradient(c,F,u)_1 = ambientGradient(F,(c,0,u0,u1))_3.

## Equal ambient gradients give equal fibre gradients

Phase 93.35 first gives

    p0 = q0.

Phase 93.37 says ambient gradient coordinates 2 and 3 ignore X1.
Therefore replacing the X1-coordinate of p and q by zero does not change
their F2/F3 values.

The new evaluation bridge then identifies those values with the common
planar fibre map at c=p0.

Thus equal ambient gradients imply equal values of the same planar fibre
map at `(p2,p3)` and `(q2,q3)`.

## JC2 recovers X2,X3

Phase 93.36 already proves that this planar fibre map is injective under
`PlanarJC2Injectivity K`.

So Phase 93.38 obtains

    p2 = q2
    p3 = q3.

## Full standard k=1 endpoint

Now:

* Phase 93.35 gives p0=q0;
* Phase 93.38 + JC2 gives p2=q2 and p3=q3;
* Phase 93.37 gives p1=q1 from equality of gradient coordinate 0.

Hence p=q.

The endpoint theorem is:

    standardOneZero_terminal_gradient_injective_of_JC2

with the collision corollary:

    standardOneZero_terminal_collision_impossible_of_JC2.

If this patch compiles cleanly, the standard-coordinate k=1 terminal
branch is closed in Lean under the existing JC2 interface.  The next
terminal work is coordinate-permutation transport for the one-zero and
two-zero standard forms, followed by assembly with the terminal weight
classification.

No previous theorem is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
