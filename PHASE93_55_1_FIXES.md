# Phase 93.55.1 — MvPolynomial extensionality fix

The first Phase 93.55 build failed only in
`integralKernelBlowupFamily_zero_eq`.

Using

    ext d

invoked recursive extensionality: after extensionality on the outer
`MvPolynomial`, Lean also descended into the coefficient type
`Polynomial K`, producing an unnecessary scalar coefficient index `n`.

The proof now uses exactly one level of extensionality:

    apply MvPolynomial.ext
    intro d

and then applies the already-green coefficient equality from Phase 93.52.

No theorem statement or mathematical content is changed.
