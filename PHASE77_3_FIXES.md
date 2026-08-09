# Phase 77.3 fixes

Phase 77.2 had one remaining elaboration failure in `quadraticAutonomous_neg_one_two_term`.

The mathematics was already established (`hqC : q = C (q.coeff 0)`), but `rw [hqC]` rewrote both the factor `q` and the occurrence of `q` inside the scalar expression `q.coeff 0`.  This changed the target to contain `(C (q.coeff 0)).coeff 0` and left a spurious simplification goal.

Phase 77.3 avoids global rewriting entirely.  It transports `hqC` through multiplication using `congrArg`, obtaining the exact local equality

```
X ^ m * q = X ^ m * C (q.coeff 0)
```

and then transports that equality through addition by `C c`.  The final commutativity step is unchanged.

No theorem statement, hypothesis, or mathematical argument changed.
