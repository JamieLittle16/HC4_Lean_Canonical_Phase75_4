# Phase 89.2 — MvPolynomial lexicographic exposure bridge

## New module

    HC4/Newton/LexicographicInitialForm.lean

Phase 89.1 proved equality of the relevant maximiser sets on an arbitrary
finite support. Phase 89.2 lifts that result to actual multivariate
polynomials.

The new definition `selectedInitial` forms a polynomial by summing exactly
the monomials of the original polynomial whose exponent satisfies a given
predicate.

The main theorem is:

    scaledInitialForm_eq_lexInitialForm

If every secondary weight on the support is `< M`, the polynomial selected
by maximising `M*w₀+w₁` is exactly the polynomial selected by lexicographic
maximisation of `(w₀,w₁)`.

This is a literal equality in `MvPolynomial`, not only equality of sets of
exponents.

## Deliberate API boundary

The older verified `HC4.Polynomial.initialForm` implementation is not
modified.  This phase proves the finite Newton--Rees bridge independently
from that representation.  The next adapter phase can identify these
selected sums with the legacy initial-form API.

## Build integration

`RankThreeInfinityAssembly.lean` receives only an additional import so the
canonical `./verify.sh` necessarily kernel-checks the new module.

No Phase 88/89 theorem statement is weakened or changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
