# Phase 91.6 — directional coefficient recurrence

## New module

    HC4/Newton/DirectionalCoefficientRecurrence.lean

Instead of implementing a general binary linear coordinate substitution,
this phase extracts the coefficient recurrence directly from the verified
directional-derivative equation.

If

    D_(u,v) F = 0,

then for every lower multi-index `m` Lean proves

    u * (m_i+1) * coeff(m+e_i)
      + v * (m_j+1) * coeff(m+e_j) = 0.

All exponents in the other variables remain frozen in `m`. Hence the
recurrence applies independently to every external coefficient slice,
which is exactly what is needed for an eventual normal form

    a(other variables) * L(i,j)^n.

The module also solves one adjacent coefficient in terms of the other when
`u ≠ 0`, with a characteristic-zero convenience theorem ensuring the
integer multiplicity is nonzero.

This replaces coordinate-change bureaucracy by the finite binomial
recurrence that directly characterises a power of a linear form.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
