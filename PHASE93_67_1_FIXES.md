# Phase 93.67.1 — Arithmetic normalisation fix

The first Phase 93.67 build reduced the large first-stop construction to
four arithmetic proof-shape errors.

## Coefficient exponent inequality

`exact_mod_cast` was being asked to interpret an intermediate
`Int.subNatNat` normal form.  The proof now explicitly changes the aligned
order inequality to

    0 <= 20*v + N*(raw - 4)

in `ℤ`, derives

    4*N <= N*raw + 20*v

with `omega`, and only then casts the clean inequality back to `ℕ`.

## Section inequalities

The three section bounds had already normalised the hypothesis using
`alignedSmithRamificationIndex = 20`, but left the target containing the
opaque constant.  The target is now normalised to literal `20` before
`omega`.

## w-coordinate exponent

The inverse Smith weight of coordinate `3` is

    2*N + 2*N,

while the divisibility theorem naturally produced `4*N`.  The proof now
records the explicit natural-number equality

    2*N + 2*N = 4*N

before the final simplification.

No theorem statement, assumption, selector, or mathematical content changes.
