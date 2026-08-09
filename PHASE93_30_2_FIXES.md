# Phase 93.30.2 — concrete derivative-evaluation equalities

Affected module:

    HC4/Newton/TerminalTwoZeroGradientConjugacy.lean

The generic helper theorems

    eval_pderiv_standardTwoZeroA_eq_planar
    eval_pderiv_standardTwoZeroC_eq_planar

are correct, but their left-hand sides retain the index expression

    standardZeroPairEmbedding 0
    standardZeroPairEmbedding 1.

After the surrounding `change`, the goal already contains the reduced
literal indices `0` and `1`, so `rw` cannot match the helper theorem
syntactically.

The repair first specialises each helper theorem and uses `simpa` to obtain
concrete equalities

    eval p (pderiv 0 Aambient) = eval u (pderiv 0 Aplanar)
    eval p (pderiv 0 Cambient) = eval u (pderiv 0 Cplanar)

and likewise for index `1`.

The main calculation then rewrites with these concrete equalities.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
