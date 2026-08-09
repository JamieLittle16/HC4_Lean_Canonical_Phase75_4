# Phase 93.72 — geometric assembly entry

This phase is the result of the first adversarial global-assembly audit
after the coupled Smith wall (93.71.2) went green.

It intentionally does **not** introduce a theorem named `JC2ImpliesHC4`.
The audit found that doing so at this point would hide real geometric data
behind the numerical `GlobalRestartState`.

## What is now formalised

### 1. Geometric restart state

`CanonicalGeometricRestartState D` carries:

- determinant defect;
- repair state;
- the actual polynomial family;
- the actual moving right marked section;
- ordinary homogeneity;
- the exact Hessian defect;
- the exact family-gradient collision from the identically-zero section;
- the canonical right reduction `e0`.

Its `.toGlobal` projection recovers the old numerical state.

### 2. Positive maximal kernel slope is genuinely re-entrant

The patch proves:

- integral kernel blow-up preserves ordinary homogeneity;
- the zero moving section stays identically zero;
- a positive blow-up in a transverse kernel coordinate preserves `e0`;
- therefore the canonical special pair stays distinct automatically;
- `canonicalGeometricRestart_positiveMaximalKernelSlope` constructs the
  complete geometric successor and proves `GlobalRestartProgress`.

This closes the main geometry-threading weakness of the positive branch.

### 3. The actual global first section has no Smith section walls

The global exact-collision normalisation uses the first section identically
zero.  The patch proves its aligned section-wall set is empty.

The specialized theorem

    alignedSmith_zeroSection_geometricDispatcher

therefore has only two outcomes:

    canonical local repair/terminal
      OR
    separated RIGHT-section wall.

There is no left-section branch.

### 4. Separated right walls are scale-quantised

The old Phase 93.70 proof only extracted a common factor `X`.

The patch proves:

- every separated right section wall has common factor `X^10`;
- its once-ramified defect becomes exactly
      20*Delta -> 20*(Delta-2);
- exact family collision is preserved;
- ordinary homogeneity is preserved;
- a y/z wall has the stronger factor `X^20`;
- a y/z wall has exact defect
      20*Delta -> 20*(Delta-4).

These facts are important because they show the old `20*Delta -> 20*Delta-4`
numerical restart was far weaker than the actual arithmetic.

## Remaining global interface exposed by the audit

A separated right-section wall moves the right marked special point away
from `e0`.  The extracted family therefore cannot simply be passed back to
the canonical zero-slope Smith dispatcher, and fresh ramification at every
iteration would not be a well-founded defect argument.

The exact remaining interface is named

    HasCanonicalContinuationFromSeparatedRightWall

It asks for a pointed chart continuation returning the moved exact
collision to the canonical zero/e0 geometric state without hiding a fresh
uncontrolled ramification.

The current Lean tree also still needs, above this restart layer:

1. the global exact-collision/Laurent extraction from an arbitrary HC4
   counterexample as Lean source;
2. a total local orchestration theorem taking the rigid rank-one/rank-two/
   mixed repair outcomes all the way to `CertifiedTerminalEndpoint`.

Those were already explicit scope boundaries in the existing
`RestartClassification.lean` and the v5 restart formalisation; Phase 93.72
does not pretend otherwise.

No `sorry`, `admit`, `axiom`, or `unsafe` is introduced.
