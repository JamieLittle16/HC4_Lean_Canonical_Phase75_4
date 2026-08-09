# Phase 93.60.3 — Induction-hypothesis normalisation fix

The Phase 93.60.2 build reduced the file to exactly two failures:

    change ... at hp

in the `add` and `mul_X` branches of
`eval_parameterRamificationFamily`.

The packaged expression

    eval section (parameterRamificationFamily D p)

is propositionally/simp-equivalent to the exposed normal form

    eval₂ ramificationHom section p,

but it is not definitionally equal.  Therefore `change ... at hp` is too
strong.

This patch derives local hypotheses `hp'` / `hq'` via

    simpa [parameterRamificationFamily] using hp

and then rewrites the already-exposed branch goals with those hypotheses.

The collision-transport theorem no longer failed in the 93.60.2 build and
is left unchanged.

No theorem statement, assumption, or mathematical content changes.
