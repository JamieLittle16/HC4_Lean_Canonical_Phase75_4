# Phase 93.38.2 — pin the fibre evaluation algebra-hom type

Affected module:

    HC4/Newton/TerminalOneZeroEndpoint.lean

The Phase 93.38.1 build progressed past the earlier `eval`/`aeval`
conversion failure.  The sole remaining error occurs in the declaration
of the local hom equality `hhom`:

    typeclass instance problem is stuck
    Algebra ?m K

The right-hand `MvPolynomial.aeval` has not yet been given enough type
information for Lean to infer its coefficient algebra before
`MvPolynomial.algHom_ext` is invoked.

## Repair

Both sides of `hhom` are explicitly annotated as

    MvPolynomial (Fin 4) K →ₐ[K] K.

This pins:

* the source variable type to `Fin 4`;
* the coefficient ring to `K`;
* the target algebra to `K`;
* the scalar algebra structure to the canonical `K`-algebra structure.

After `MvPolynomial.algHom_ext` proves the two homs equal on the four
variables, the equality is applied to `P` using an explicit `congrArg`
rather than relying on another specialised congruence API.

No theorem statement, mathematical hypothesis, proof strategy, or
heartbeat setting changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
