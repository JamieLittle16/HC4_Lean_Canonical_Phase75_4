# Phase 75.14.2 — Prop-valued terminal extraction fix

`HasRigidClosingTerminalExtraction` was declared to return `Prop`, but its body
was a function into the Type-valued structure `TerminalAssociatedGradedCollisionData K`.
Lean correctly rejected that universe mismatch.

This patch keeps the interface proof-irrelevant by asking for a `Nonempty`
terminal datum for every provenance-preserving closing certificate:

```lean
def HasRigidClosingTerminalExtraction ... : Prop :=
  ∀ _hclosing : f.RigidClosingCertificate,
    Nonempty (TerminalAssociatedGradedCollisionData K)
```

The JC2 consumer destructs that `Nonempty` witness and applies the already-proved
terminal contradiction theorem. No mathematical hypothesis is added or weakened;
this only gives the intended interface the correct sort.
