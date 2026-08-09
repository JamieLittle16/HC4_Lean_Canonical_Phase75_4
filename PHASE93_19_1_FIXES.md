# Phase 93.19.1 — special-fibre evaluation API repair

Affected file:

    HC4/Valuation/PolynomialFamilyCollisionSpecialFiber.lean

The only Phase 93.19 build failure was the unavailable convenience theorem

    MvPolynomial.map_eval.

The commutation identity is now proved using two older/stable primitives:

    MvPolynomial.eval_map
    MvPolynomial.eval₂_comp.

After `pderiv_map`, the left-hand side becomes

    eval (constantCoeff ∘ a) (map constantCoeff Q).

`eval_map` rewrites this to

    eval₂ constantCoeff (constantCoeff ∘ a) Q.

The theorem `eval₂_comp` identifies this with

    constantCoeff (eval a Q),

which is exactly the required right-hand side.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
