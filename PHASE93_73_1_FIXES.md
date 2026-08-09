# Phase 93.73.1 — shear-core simplification

The first 93.73 compile log contained many diagnostics, but they came from
two brittle implementation choices rather than many mathematical failures.

## 1. Keep the shear ring hom opaque

The old partial-derivative induction repeatedly unfolded
`elementaryShearHom`.

That exposes mathlib's internal `bind₁` representation of `eval₂Hom`, so the
induction hypotheses cease to match syntactically.

The new proof adds only two public simp lemmas:

    elementaryShearHom_C
    elementaryShearHom_X

and performs `MvPolynomial.induction_on` while keeping the ring hom opaque.

The multiplication-by-variable step now uses only:
- `map_mul`;
- `MvPolynomial.pderiv_mul`;
- `map_add`;
- the induction hypothesis;
- the explicit linear shear variable.

This removes the entire `bind₁` error cluster.

## 2. Hessian covariance uses explicit row/column identities

The Hessian proof is retained, but each of its four `(i=0?/j=0?)` branches
now introduces the exact transvection row/column identity as a named
equality before rewriting.

The `j != 0` branch explicitly expands `pderiv` over the sum created by the
longitudinal chain rule before applying the transverse derivative theorem.

## 3. Special-point cleanup

- use `(0 : Fin 4) != k`, not `k != 0`, for the `if 0 = k` simplifier;
- convert the longitudinal special-point hypothesis to an explicit
  constant-coefficient equality before simplification;
- close the `Fin 4` coordinate cases with `simpa using` rather than rewriting
  through the elaborator's internal Fin literals.

## 4. Remove the premature wall split

The y/z-vs-w decomposition at the end of the first 93.73 draft was not
needed for the pointed-continuation theorem and generated a large,
independent elaboration cascade.

It is removed from this patch.

Phase 93.73.1 now has one purpose only:

    separated right wall
      -> X^10 extraction
      -> determinant-one pointed shear
      -> canonical 0/e0 collision family.

The physical scale descent is deliberately deferred to the next phase.

No theorem assumption is weakened.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
