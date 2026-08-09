# Phase 93.72.2 — field projection fix

The Phase 93.72.1 build reduced the file to one compile error.

The geometric state field is named

    sectionSpecial

but one stale projection remained as

    s.movingSectionSpecial.

This patch changes that single projection to

    s.sectionSpecial.

No theorem, definition, assumption, or proof argument changes.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
