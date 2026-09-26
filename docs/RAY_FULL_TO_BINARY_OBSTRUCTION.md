# Step 3: exact Hessian-one test of binary determinant extraction

The actual `.pr` ray clock is proved in
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayExactSchurClock`.
Its preterminal mixed coefficient is not yet a terminal contradiction.
This audit tests the alternative full-to-binary determinant implication.

Take coordinates `(x,y,z,w)` and the polynomial

`F = x*y + z*w + x^3*z^3`.

Its four-variable Hessian determinant is exactly 1. With positive weights
`(2,2,2,2)` and exact maximal source level 12, its reverse Rees is

`R = t^8*x*y + t^8*z*w + x^3*z^3`.

Here `det Hess R = t^32`, and the quadratic margin is `2*12 < 32`.
Inflating the three transverse coordinates by `t^2` gives the binary family

`Q = t^10*x*y + t^12*z*w + t^6*x^3*z^3`.

Its full Hessian determinant is exactly `t^44`. Both reverse-Rees and binary
Euler identities hold exactly; these are not truncated determinant equations.
The profile rows have precisely the repository's Euler-scaled definitions:

- `H00 = t^2 * d_t^2 Q`;
- `H01 = t*x * d_t d_x Q`;
- `H11 = x^2 * d_x^2 Q`.

Nevertheless the coefficient of `t^20` in `H00*H11-H01^2` is
`-100*x^2*y^2`, which is nonzero. Order 20 is the exact quadratic profile order
`2*12 - 2*2`, strictly below the full clock 44. Thus full determinant-layer
vanishing does not imply binary profile-layer vanishing under these hypotheses.

`tools/research/ray_full_to_binary_probe.py` verifies every identity above with
exact SymPy polynomial arithmetic. This is a symbolic diagnostic, not a Lean
certificate and not a counterexample to HC4 or to the complete terminal package.
The initial source `x^3*z^3` has Hessian rank two and does not supply the retained
rank-three other-facet ray or its nonzero constant rank-one Schur block.

## Consequence for the attempted closing proof

This rules out proving the binary vanishing statement using only Hessian-one,
positive reverse-Rees weights, the quadratic margin and Euler bookkeeping.
It does not rule out deriving it using the additional retained rank-three
endpoint and first-departure geometry. A valid proof still needs to identify
and control the coupling terms with those hypotheses. The existing
`profileHessianDet_eq_zero_of_binaryFamily_layers` theorem assumes vanishing
of the binary profile determinant's layers; the available full Hessian-layer
vanishing theorem does not discharge that assumption.

No source-honest global progress, other-facet impossibility or unrestricted
HC4 theorem is established by this audit. Step 3 remains open.
