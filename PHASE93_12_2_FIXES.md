# Phase 93.12.2 — pinned homogeneity and pure-axis product repair

Affected file:

    HC4/Newton/SmithFirstWallTransverse.lean

The Phase 93.12.1 build exposed the exact pinned representation of
`MvPolynomial.IsHomogeneous D`.

## Homogeneity

On this Mathlib revision, `hhom : F.IsHomogeneous D` is directly a theorem

    coeff d F != 0 -> Finsupp.weight 1 d = D.

The failed structure-style field call is removed.

From `hd : d ∈ F.support`, the repaired proof obtains

    hcoeffd : coeff d F != 0

and then

    hdeg : Finsupp.weight 1 d = D := hhom hcoeffd.

After rewriting the already-proved contributor shape

    d = single x (d x) + single i 1,

the additive weight simplifier gives

    d x + 1 = D.

No `Finsupp.degree` API is used.

## Pure-axis remainder evaluation

The blocker contribution proof no longer asks `simp` to prove
nonvanishing of a general Finsupp product.

After the exact derivative-remainder theorem rewrites the remainder to

    single x (D-1),

the proof explicitly evaluates its product using

    Finsupp.prod_single_index.

At the coordinate-axis point this product is exactly `1`, so the whole
gradient contribution reduces to the already-known nonzero coefficient.

Two linter-reported unused simp arguments are also removed.

No theorem statement is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
