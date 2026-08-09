# Phase 93.8 — Smith valuation-tilt adapter

## New module

    HC4/Newton/SmithValuationTiltAdapter.lean

This phase connects the relative Levi grade to an actual conformal
valuation change.

For a monomial `x^a y^b z^c w^d`, a two-parameter conformal tilt
`theta=(theta_1,theta_2)` changes the raw monomial weight by

    theta_1*b + theta_2*c + (theta_1+theta_2)*d

and changes the normalising Levi reference by

    theta_1+theta_2.

Lean proves the exact identity

    normalised tilt change
      = theta dot (b+d-1, c+d-1).

This is the formal Smith valuation adapter promised by the restart proof.

A useful strengthening is also proved.  Since every Smith-grade coordinate
is at least `-1`, any nonnegative tilt direction satisfies the universal
bound

    theta dot Gamma >= -(theta_1+theta_2).

For the explicit Phase 93.6 separator

    theta = (2k, k*l+1)

the support-independent natural bound is

    B = 2k + k*l + 1.

The final theorem

    smithFiniteSupportTilt_strictly_raises_minimum

combines that bound with the green Phase 93.7 small-tilt theorem: if every
old minimal-face monomial has positive separator value, the explicit
rational conformal tilt raises every supported normalised valuation
strictly above the old minimum.

The remaining pole-balance step is now a minimality interface: formalise
what it means for the pointed Laurent model to be pole-minimal among legal
integral conformal tilts, and observe that the theorem above contradicts
that property whenever a Smith separator exists.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
