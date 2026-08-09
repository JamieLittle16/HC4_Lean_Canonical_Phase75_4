# Phase 93.38.1 — pinned aeval/eval endpoint bridge repair

Affected module:

    HC4/Newton/TerminalOneZeroEndpoint.lean

The Phase 93.38 build reaches only the general fibre-evaluation bridge.
No later endpoint theorem is implicated yet.

Two API mistakes caused the failure:

1. after `comp_aeval_apply` and `aeval_rename`, the goal is equality of
   two bundled `MvPolynomial` algebra homomorphisms.  Ordinary `funext`
   is not the appropriate extensionality principle;

2. the pinned API has no theorem named
   `MvPolynomial.aeval_eq_eval`.

## Pinned API

In the pinned Mathlib source:

    @[simp]
    lemma coe_aeval_eq_eval :
      RingHomClass.toRingHom (MvPolynomial.aeval f)
        = MvPolynomial.eval f := rfl

so evaluation over the coefficient field is definitionally the same
underlying ring hom as `aeval`.

The pinned `MvPolynomial.algHom_ext` theorem says that two algebra
homomorphisms out of a multivariate polynomial ring are equal once their
values on every `X i` agree.

## Repair

The proof now:

* `change`s the scalar `eval` equation directly to the corresponding
  `aeval` equation;
* composes evaluation with the fibre substitution;
* pushes evaluation through `rename`;
* proves the resulting two `aeval` algebra homs equal using
  `MvPolynomial.algHom_ext`;
* checks the four variable images by `fin_cases`;
* applies the hom equality to `P` using `AlgHom.congr_fun`.

No mathematical statement, hypothesis, endpoint strategy, heartbeat
setting, or previous theorem changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
