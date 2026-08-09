# Phase 81.1 fixes

Phase 81 failed at one proof-shape step in `FinitePreimage.lean`.

The hypothesis was

```lean
hroot : (N - C y * D).eval x = 0
```

and the proof attempted to use `change` to replace this by

```lean
N.eval x - y * D.eval x = 0
```

These expressions are propositionally equal after evaluation simplification, but not definitionally equal, so `change` was invalid.

Phase 81.1 replaces that step with the same pinned-Mathlib-compatible pattern already used later in the file:

```lean
have h : N.eval x - y * D.eval x = 0 := by
  simpa using hroot
```

No theorem statements, hypotheses, definitions, or downstream proofs changed.
