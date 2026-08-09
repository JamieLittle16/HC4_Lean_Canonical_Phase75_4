# Phase 93.53.1 — Finsupp product bridge

`MvPolynomial.eval_eq'` expands a monomial using `Finsupp.prod`, so the
evaluation proof saw

    d.prod (fun n e => section n ^ e)

rather than the full finite product used by the Phase 93.53 monomial lemma.

This patch inserts `Finsupp.prod_fintype` to rewrite the finitely-supported
product as the full product over `Fin 4`.  The zero-exponent condition is
discharged by `simp` (`x^0 = 1`).

After that rewrite, the existing
`fin4_kernelBlowupSection_monomialProduct` theorem applies directly.

No theorem statements or mathematical content are changed.
