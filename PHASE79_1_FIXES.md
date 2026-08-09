# Phase 79.1 fixes

Phase 79 failed at one local coefficient simplification in
`coeff_n_mul_natDegree_shiftedAutonomousClearedRHS`.

The summand was parsed as

```lean
(Polynomial.C (R.coeff j) * A) * B
```

but the proof used `← mul_assoc`, which looks for an already right-associated
term `C * (A * B)`.  Phase 79.1 changes this to ordinary `mul_assoc`, producing

```lean
Polynomial.C (R.coeff j) * (A * B)
```

so the already-used theorem `Polynomial.coeff_C_mul` can reduce the goal to
the previously proved coefficient vanishing `hzero`.

No definitions, theorem statements, hypotheses, or mathematical arguments
change.
