# Phase 88.4 fixes

## 1. Cleared rational identity

Phase 88.3 left an inverse-power expression after `field_simp`, which `ring`
could not close. Phase 88.4 isolates the exact cancellation

    eta * ι(D)^2 = ι(H)

from the supplied representation of `eta`, then completes the mapped
polynomial identity by ordinary commutative-ring rearrangement.

## 2. Pinned RatFunc compatibility

The Phase 88.3 backport copied a later Mathlib shape too literally. In
particular, the pinned revision does not support the later `K[f]` notation or
several later simp lemmas.

Phase 88.4 instead builds the relation

    num(f) - gen(f) * denom(f)

directly as a polynomial over `K⟮f⟯`, where `gen(f)` is the generator of the
simple intermediate field. Its evaluation at the ambient rational-function
variable is proved using APIs present in the pinned revision.

This relation proves `X` algebraic over `K⟮f⟯` whenever `f` is nonconstant.
If `f` were algebraic over `K`, restriction of scalars would make `X`
algebraic over `K`, contradicting `RatFunc.transcendental_X`.

## Audit

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
