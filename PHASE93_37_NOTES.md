# Phase 93.37 — ambient decoupling and final-coordinate recovery

Built against the clean Phase 93.36.2 tree.

Phase 93.36 gives JC2-injectivity of every fixed standard one-zero planar
fibre.  This phase proves the ambient independence statements needed to
connect an arbitrary four-dimensional collision to that fibre and then
recover the last source coordinate.

## Generic derivative-zero evaluation invariance

Over characteristic zero:

    pderiv i P = 0

implies that every supported monomial of P has exponent zero in coordinate
i.  Therefore two points agreeing off coordinate i give equal evaluations
of P.

The theorem is:

    eval_eq_of_pderiv_eq_zero

and is proved using the already-green
`exponent_eq_zero_of_pderiv_eq_zero` and monomial evaluation lemma from
Phase 93.33.

## Gradient coordinates 2 and 3 ignore X1

The green one-zero sparse Hessian row gives

    pderiv 2 (pderiv 1 F) = 0
    pderiv 3 (pderiv 1 F) = 0.

Mixed-partial commutation therefore yields

    pderiv 1 (pderiv 2 F) = 0
    pderiv 1 (pderiv 3 F) = 0.

Hence F_2 and F_3 are unchanged when only X1 changes.

## Gradient coordinate 0 is affine in X1 modulo an X1-independent remainder

Phase 93.35 gives

    S = pderiv 0 (pderiv 1 F) = C s,  s != 0.

By mixed-partial symmetry,

    pderiv 1 (pderiv 0 F) = C s.

Therefore

    pderiv 0 F - C s * X 1

has zero partial derivative in coordinate 1 and is independent of X1.

## Final coordinate recovery

If p and q already agree in coordinates 0,2,3 and their gradient
coordinate 0 values agree, the X1-independent remainders cancel, leaving

    s * p1 = s * q1.

Since s != 0,

    p1 = q1.

Thus, after the planar fibre recovers coordinates 2,3, the final ambient
coordinate is forced automatically.

The only missing standard-k=1 endpoint bridge after this phase is the
evaluation identification between the ambient F_2,F_3 values and the
already-green fixed-X0 planar fibre map.

No previous theorem is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
