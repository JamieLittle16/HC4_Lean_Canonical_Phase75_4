# Phase 93.33.3 — endpoint slice simplification

Affected module:

    HC4/Newton/TerminalPositiveWeightEndpoint.lean

The build reached the final coordinate step of the strong-induction proof.

After the weight-block kernel theorem, we have

    hvi :
      terminalWeightSliceDifference
        lambda (lambda i) p q i = 0.

By definition,

    terminalWeightSliceDifference lambda t p q i
      =
    if lambda i = t then p i - q i else 0.

At `t = lambda i`, this is exactly `p i - q i`, but the previous
`dsimp`/`simp` sequence did not reduce the local `let`-bound slice far
enough for `sub_eq_zero.mp`.

The repair derives the concrete equality explicitly:

    have hdiff : p i - q i = 0 := by
      simpa [v, t, terminalWeightSliceDifference] using hvi

and then concludes with `sub_eq_zero.mp hdiff`.

No theorem statement, hypothesis, or mathematical argument changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
