# Phase 90.5.1 fix

Affected file:

    HC4/Newton/RankTwoReesSchurEntry.lean

The theorem `tail_scaledDeterminant_eq_schurDeterminant` had already rewritten
the three factored Schur entries back to `block.schurA`, `block.schurB`,
and `block.schurC`. The remaining goal was exactly the definitional body of
`PolynomialRankTwoFourBlock.schurDeterminant`.

Phase 90.5.1 closes that final definitional equality with `rfl`.

No mathematical or theorem-statement change is made.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
