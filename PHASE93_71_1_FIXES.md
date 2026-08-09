# Phase 93.71.1 — local coupled-wall closure fix

The first Phase 93.71 build left a small collection of local elaboration
and simplifier issues.  The coupled-wall mathematical argument is unchanged.

## Fixes

1. Residual-order arithmetic
   - unfold the local genuine-wall abbreviation `N` before normalising the
     integer inequality;
   - this aligns the positive residual hypothesis and target syntactically.

2. Negative Smith-pattern disjunction
   - correct the nesting of
       Pure ∨ First ∨ Second
     as `Pure ∨ (First ∨ Second)`.

3. Blocker inequality helpers
   - remove invalid `(K := K)` arguments from purely combinatorial exponent
     lemmas.

4. Three-blocker reconstruction
   - the invalid named-argument failures that interrupted the extensionality
     proof are removed.

5. Gradient calculations
   - remove a redundant `ring_nf` after the y-gradient `simp` already closes
     the goal;
   - disable the unrelated simp theorem
       `standardTwoZero_pderiv_two_eq_A`
     during the z-gradient calculation, so simplification remains on the
     explicit three-blocker algebraic model.

6. Longitudinal coefficient
   - after simplification, the x-gradient collision is already the
       `(D : K) = 0 ∨ A = 0`
     disjunction;
   - consume that disjunction directly using characteristic zero instead of
     trying to reconstruct a product-zero equation.

No theorem statements or assumptions are changed.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
