# First-interior adapter audit — 13 September 2026

Audited base: `509785f68426bfaf7137d8419154998898c9712d`, PR #34.

## Status

This patch is **SOURCE CANDIDATE, NOT LEAN VERIFIED**. It does not close
`NoStrictInteriorSupport` or claim unrestricted HC4.

The first-interior module now adds three source-derived lemmas:

- `parameterLayer_coeff_eq_carrier_of_mem`: exact supported parameter-layer
  coefficients equal the original planar carrier coefficients.
- `firstPositiveLayer_quotient_fiber`: the first layer has one full quotient
  coordinate, using the existing carrier `pair_fiber` theorem.
- `exists_firstPositiveLayer_strictInterior_fiber`: shared pair degree and
  transverse height, strict-interior bounds, and literal coefficients for
  every supported monomial of the selected layer.

These advance A1. They do not yet identify the two Euler-Hessian moment
matrices required by `PlanarContactFirstVariationBridge`.

## Additional A2 obligation: degree bound

`affineTwoRoot_degreeOne_primitive` explicitly requires
`phi.natDegree <= 1`. The live staircase classification gives bounds on
quotient pair degree and transverse height; it does not state this bound
on the omitted-coordinate coefficient polynomial. The existing primitive
highest-slice theorem concerns the highest slice. The selected first
strict-interior layer is strictly below it.

The following exact calculation shows that the staircase arithmetic and
first-variation equation alone cannot supply the missing degree bound.
Take `V=2`, `ell=4`, highest pair degree `n=3`, first pair degree `k=2`,
height `j=2`, and locked coefficients `a=b=1`.

Then `A=a(ell+1)=5`, `B=b*ell=4`, and

```text
phi(T) = (5+4T)^2 = 25+40T+16T^2.
(5+4T)^2 phi'' - 8(5+4T) phi' + 32 phi = 0.
```

This is precisely the existing affine two-root operator with lower root
`k-1=1`, but `deg(phi)=2`.

Its three honest monomial exponents are

```text
(0,2,3,8), (1,1,2,6), (2,0,1,4).
```

All have quotient coordinate `(2,3,8)` for direction `(1,-1,-1,-2)`.
They satisfy the staircase equations

```text
(n-1)j = ell(n-k) = 4,
secondTransverse = V(k+j) = 8.
```

The top contact degree is `(V+1)(ell+1)+1=16`. With the existing contact
weight (ordinary degree plus `(V+1)e0`), each exponent has contact order
`3`, strictly between zero and the highest order `6`. Also
`1<k<n` and `0<j<ell`.

The polynomial residual and all these integer identities were checked with
exact integer arithmetic. This is **not** a counterexample to the live
frontier or HC4: no full singular carrier, terminal state, or collision
provenance has been constructed. It isolates the insufficiency of this
subset of the proposed inputs.

**OPEN formalisation obligation:** derive the degree bound from additional
live source/contact data, or use higher-order singularity information to
exclude higher-degree first profiles. Do not insert the bound as an extra
frontier assumption. A3 also still needs its source-derived incompatibility
proof; the schematic name in the attached plan is not a live declaration.

## Verification environment

The exact base-head GitHub Actions run `34762060237` reports
`action_required`; its jobs endpoint returns an empty list. Thus that run
does not certify the base head.

Lean 4.24.0 was installed locally, but its executable fails at startup with
`error: failed to locate application`. Lake reports that it cannot detect
its installation configuration. Explicit `LEAN_SYSROOT` did not fix this.
No successful Lean invocation or build is claimed. `git diff --check`
passes for this patch.

Once execution is available, compile
`HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorFirstLayer`
first, then complete the moment representation adapter. Resolve the degree
obligation before using `affineTwoRoot_degreeOne_primitive` in the live branch.
