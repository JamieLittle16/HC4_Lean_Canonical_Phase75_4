# Phase 93.63.1 — Rees support and elaboration fix

The first 93.63 build exposed a coefficient-type mismatch hidden by the
notation.

## Rees-family projected support

The older Newton definition `smithProjectedSupport` was introduced for
field-valued special-fibre polynomials and therefore has a `[Field K]`
coefficient assumption.

The family in Phase 93.63 has coefficients in `Polynomial K`, which is not
a field.  The projected support operation itself does not use division, so
this patch defines the correct coefficient-ring-agnostic object

    smithAxisProjectedSupport P := P.support.image smithAxisProjection.

All strict-improvement hypotheses on the Rees family now use this support.

The special-fibre Smith classifier from Phase 93.62 remains unchanged and
continues to use the original field-valued projected support.

## Product normalisation

`smithConformalCoefficientFactor` is explicitly unfolded before
`Fin.prod_univ_four`, exposing the finite product that theorem rewrites.

## Section powers

Hypotheses `X | a i` are explicitly normalised to `X^1 | a i` before
calling `parameterRamification_pow_dvd`.

## Elaboration robustness

Key helper calls in the dependent final theorem now pass `(K := K)`
explicitly, preventing unresolved coefficient-field metavariables from
propagating into `let` bindings.

No mathematical statement of the fixed-scale restart is weakened.
