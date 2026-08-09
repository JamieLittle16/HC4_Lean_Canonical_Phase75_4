# Phase 93.59.1 — Product normalisation fix

The initial 93.59 build exposed three local proof-script issues only.

1. In `eval_integralSmithConformalFamily`, simplification had already put
   the inflated-side monomial product into a full `Fin 4` product.  The only
   remaining `Finsupp.prod` was the unscaled `a` product on the left.
   The proof now converts that product instead, after which
   `fin4_smithConformalInflateSection_monomialProduct` matches directly.

2. `prod_smithConformalDerivativeCoefficient` was already closed by `simp`;
   the trailing `ring` caused `No goals to be solved`.

3. The same happened in the constant Hessian-scaling product calculation;
   the redundant trailing `ring` has been removed.

No theorem statement, assumption, or mathematical content is changed.
