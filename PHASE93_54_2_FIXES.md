# Phase 93.54.2 — Derivative algebra fixes

This patch addresses the three remaining root errors from the 93.54.1 build.

## 1. Pin the coefficient field

`kernelCoefficientTauPower_sub_single_of_ne` compared two calls to
`kernelCoefficientTauPower` without another expression fixing the
coefficient field. Lean therefore left the `Field` metavariable stuck.

Both calls now explicitly use:

    kernelCoefficientTauPower (K := K) ...

## 2. Replace fragile `omega` exponent arithmetic

For `d(kernel) > 0`, the proof now reconstructs

    d(kernel) - 1 + 1 = d(kernel)

using `Nat.sub_add_cancel`, then derives

    slope + slope * (d(kernel) - 1)
      = slope * d(kernel)

by `Nat.mul_add` and commutativity. This avoids nonlinear/subtraction
normalisation in `omega`.

## 3. Reassociate the kernel derivative monomial

After `pderiv_monomial`, the target contains coefficient factors between
`tau^slope` and the monomial product. The earlier direct `rw` could not see
the product lemma syntactically.

The proof now:
- stores the product identity as `hprod`;
- reassociates/commutes coefficient factors with `ring`;
- rewrites by `hprod`;
- closes by `ring`.

No theorem statements or mathematical content are weakened.
