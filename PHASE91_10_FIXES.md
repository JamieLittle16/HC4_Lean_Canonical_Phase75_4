# Phase 91.10 — MvPolynomial transverse-slice classification

## New module

    HC4/Newton/TransverseSliceClassification.lean

This phase reconnects the scalar recurrence classification to an actual
multivariable polynomial.

For a frozen external exponent vector `r` with `r i = r j = 0`, define

    d_k = r + k*e_i + (n-k)*e_j

and

    c(k) = coeff d_k F.

For `k<n`, Phase 91.6 is applied at

    m_k = r + k*e_i + (n-1-k)*e_j.

The module proves the two exact index identities

    m_k + e_i = d_(k+1)
    m_k + e_j = d_k

and hence obtains

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0.

The main theorem

    transverseSlice_eq_linearPowerProfile

then invokes the green Phase 91.9 recurrence classification and proves that
every frozen external degree-`n` coefficient slice is a scalar multiple of
the profile of `(v*X-u*Y)^n`.

The expanded theorem

    transverseSlice_eq_binomialProfile

gives the explicit coefficient formula.

This is the coefficientwise form of `a(X) * L(Y)^n`: the scalar may vary
with the frozen exponents in the non-transverse variables, while the entire
transverse coefficient profile is forced to be the same linear-form power.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
