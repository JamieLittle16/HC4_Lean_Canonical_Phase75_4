# Phase 93.69 — Primitive Smith endpoint normalization

Built over the green Phase 93.68.1 tree.

This is the large local endpoint adapter following the scale-safe genuine
wall theorem.

## Ramification primitives

The patch identifies `parameterRamificationHom D` with Mathlib's polynomial
`expand`, proving:
- positive ramification is injective on nonzero coefficients;
- constant coefficients are preserved;
- exact primitive parts remain primitive after ramification.

## Coefficient wall

For a source coefficient

    c = X^v * u,  u(0) != 0,

the exact aligned wall identity cancels the Smith numerator against the
conformal multiplier.  The transformed coefficient is exactly the ramified
primitive part.

Therefore it survives on the transformed special fibre.

Since the wall derivative is negative, this directly proves

    genuineCoefficientWall_specialFiber_symmetricMinimal.

So the coefficient-wall endpoint is fully converted into the green
symmetric-minimal interface.

## Section wall

A parallel exact cancellation theorem proves that at a section wall the
corresponding transformed marked coordinate is precisely primitive and has
nonzero special value.

This yields the concrete residual certificate

    HasAlignedSmithSectionBoundary.

This is deliberately not conflated with a one-zero/two-zero terminal
weight; the latter is a statement about the potential's weight pattern.

## No-wall primitive normalization

The patch defines the finite zero-grade support and selects its minimum
exact coefficient order `m`.

It then takes one aligned Smith step

    N = 10*m.

Every normalized coefficient has residual parameter order at least `20*m`.
A generic margin theorem turns this into a common factor `X^(20*m)`.

After extracting that common factor, a zero-grade coefficient of minimal
order becomes primitive and survives on the special fibre.  Hence the
resulting special fibre is symmetric minimal.

The resulting family is

    noWallPrimitiveSmithFamily.

The patch also proves:
- arbitrary common-factor exact defect:
      Delta -> Delta - 4*n;
- ordinary homogeneity preservation through Smith/common-factor operations;
- exact Hessian defect of the primitive no-wall family;
- exact collision preservation (existential transformed marked sections).

## Headline theorem

    alignedSmith_primitiveEndpoint_dichotomy

returns:

1. genuine wall:
   - symmetric-minimal transformed special fibre, or
   - concrete section-boundary certificate;

or

2. no genuine wall:
   - one-shot primitive normalized special fibre is symmetric minimal.

Thus the only residual endpoint geometry is the marked-section boundary
certificate.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
