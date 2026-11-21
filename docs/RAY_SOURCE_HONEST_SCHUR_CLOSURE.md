# Source-honest first-ray Schur closure

**Status: PAPER CANDIDATE — not yet Lean-verified.**

This note records a paper-level closure of the rank-three `.qs` lower-ray branch whose outside endpoint is rank three on one of `.pr`, `.sp`, `.rq`.

It deliberately does **not** identify the positive auxiliary reverse-Rees clock with the original zero-defect blocker. In fact the proof below does not use the auxiliary ray clock at all. The only source-provenance input is the already-formal A19.104a theorem that the finite-support ray is an exact initial form of the represented zero-defect source.

The remaining same-carrier codimension-two branch is separate and is not addressed here.

## 1. Exact source carrier

Let `T` be the producer-free zero-strict-low singular terminal, let

```text
F = polynomialFamilySpecialFiber T.terminal.blocker.presented.family,
```

and let `C` be a lower first-nonfacet cross-facet carrier starting on `.qs`.

A19.104a gives an integer weight `W` and level `L` such that

```text
initialForm W L F = C.ray.face.
```

Thus the ray polynomial

```text
G := C.ray.face
```

is literally an exact exposed face of the actual represented determinant-one source. No reverse-Rees presentation is introduced in this step.

## 2. Uniform normal form for all three other facets

Assume the starting endpoint `v := C.ray.facetExponent` is rank three on `.qs`, and the outside endpoint `u := C.ray.outsideExponent` is rank three on another coordinate facet.

Let `j ∈ {1,2,3}` be the coordinate omitted by the outside facet, and let `{k,l} = {1,2,3} \ {j}`. Thus:

* `.pr`: `j=1`, active pair `(k,l)=(2,3)`;
* `.sp`: `j=2`, active pair `(k,l)=(1,3)`;
* `.rq`: `j=3`, active pair `(k,l)=(1,2)`.

The already-formal degree-one ray and endpoint arithmetic give

```text
v_0 = 0,   v_j = 1,
u_0 = 1,   u_j = 0,
```

and, writing

```text
B = v_k,   C = v_l,
Q = u_k,   R = u_l,
```

all four numbers are positive and

```text
B*R = C*Q,
Q < B,
R < C.
```

Because the ray is supported on a rank-three line with line length one, its coefficient polynomial has degree at most one. Both endpoint coefficients are nonzero. Therefore

```text
G = a * x_j * x_k^B * x_l^C
  + b * x_0 * x_k^Q * x_l^R
```

for nonzero `a,b : K`.

Put

```text
g = a * x_k^B * x_l^C,
f = b * x_k^Q * x_l^R,
```

so `G = x_j*g + x_0*f`.

## 3. Direction lock on the two cross-Hessian rows

Use `(x_k,x_l)` as the active pair and `(x_0,x_j)` as the complementary pair.

Let

```text
p = (∂_k f, ∂_l f),
q = (∂_k g, ∂_l g).
```

Define the nonzero scalars/polynomial

```text
alpha = a * B,
beta  = b * Q,
m      = x_k^(B-Q) * x_l^(C-R).
```

Since `B*R = C*Q`, direct differentiation gives the division-free vector identity

```text
beta * q = alpha * m * p.                       (1)
```

Indeed the `k` component is immediate, while the `l` component is exactly the cross-product relation `B*R=C*Q`.

The inequalities `Q<B` and `R<C` imply `m` has strictly positive exponent in each active variable.

## 4. Cleared Schur block is a moving rank-one line

Let `M` be the active `2 x 2` Hessian block of `G` in `(x_k,x_l)`. Because `G` is linear in both complementary variables `x_0,x_j`, its complementary `2 x 2` Hessian block is zero.

Write the denominator-cleared Schur block as

```text
S = [[A, H],
     [H, C0]].
```

By the defining adjugate formula,

```text
A  = - p^T adj(M) p,
H  = - p^T adj(M) q,
C0 = - q^T adj(M) q.
```

Applying (1), without dividing by `alpha` or `beta`, gives

```text
beta * H   = alpha * m * A,                     (2)
beta^2*C0  = alpha^2*m^2*A.                     (3)
```

Equation (3) also gives the rank-one Schur relation. Multiplying `A*C0-H^2` by `beta^2` and using (2)--(3) yields

```text
beta^2 * (A*C0 - H^2) = 0.
```

Since `beta ≠ 0`, the polynomial ring is a domain and therefore

```text
A*C0 = H^2.                                     (4)
```

## 5. The second Schur diagonal is nonzero

For the above ordering, `C0` is exactly the principal `3 x 3` Hessian minor on the coordinates `{j,k,l}`. But `{j,k,l}={1,2,3}` in all three cyclic cases.

The already-formal theorem `qs_ray_transverseHessianMinor_ne_zero` proves

```text
rayTransverseHessianMinor G ≠ 0
```

from the rank-three starting endpoint alone. Hence

```text
C0 ≠ 0.                                         (5)
```

Equation (3), together with nonzero `alpha`, `beta`, `m`, now forces

```text
A ≠ 0.                                          (6)
```

This is the key use of the retained rank-three endpoint geometry which is absent from the generic Hessian-one countertest in `RAY_FULL_TO_BINARY_OBSTRUCTION.md`.

## 6. The constant-kernel-line branch is impossible

Differentiate (2) in the active coordinate `x_k`. Since `alpha` and `beta` are scalars,

```text
beta * ∂_k H = alpha * ((∂_k m)*A + m*∂_k A).
```

Multiply by `A` and subtract `(2) * ∂_k A`. This gives the exact projective-wedge identity

```text
beta * (A*∂_k H - H*∂_k A)
  = alpha * A^2 * ∂_k m.                        (7)
```

Now

```text
∂_k m = (B-Q) * x_k^(B-Q-1) * x_l^(C-R).
```

Every factor on the right side of (7) is nonzero:

* `alpha ≠ 0` because `a ≠ 0`, `B>0`, and the field has characteristic zero;
* `A ≠ 0` by (6);
* `B-Q>0`, so its image in `K` is nonzero in characteristic zero;
* the monomial is nonzero.

Therefore

```text
A*∂_k H - H*∂_k A ≠ 0.                          (8)
```

This is exactly the raw binary Schur projective wedge. Consequently the constant raw Schur kernel-line alternative cannot occur on any of the three rank-three other-facet rays.

## 7. The moving ray carries an explicit rank-two Schur source

From (4), differentiate the rank-one relation. The standard B38 algebra gives

```text
A^2 * det(∂_k S)
  = -(A*∂_k H - H*∂_k A)^2.                    (9)
```

By (8), the right side is nonzero. Hence

```text
det(∂_k S) ≠ 0.                                (10)
```

Thus the exact exposed ray carries a genuine nondegenerate binary derivative-Schur block. Over the present characteristic-zero algebraically closed field, a nonzero determinant polynomial may be evaluated at a source point where it remains nonzero, giving a literal field-valued binary block with trivial kernel. This is the same geometric payload retained by the existing B38 `RawSpecialSchurDerivativeRankTwoRepairData`.

## 8. Source-honest global consumption

The geometry above lives on

```text
G = initialForm W L F,
```

where `F` is the actual special fibre of `T.terminal.blocker.presented.family`. Therefore the correct formal adapter should **not** construct a new positive-clock source state and should not compare clocks.

Instead introduce a geometry packet tied to the presented blocker which retains:

1. the lower first-nonfacet carrier `C`;
2. the direct initial-form equality `initialForm W L F = G`;
3. the cyclic active pair and source direction;
4. the nonzero raw Schur wedge (8);
5. the derivative negative-square identity (9);
6. a point-valued nondegenerate derivative Schur block.

This packet is the exact exposed-face analogue of the already-existing wall-face and B38 geometry packets.

Once that geometry exists, use the existing presented-blocker rank-promotion pattern. The reached source has

```text
state.repair = rankOneRepairState 0,
```

and the certified presentation preserves repair. Put

```text
target = T.terminal.blocker.presented.withRepairOnly (rankTwoRepairState 0).
```

The existing `rankOne_to_rankTwo_repairProgress 0` gives certified same-scale progress on the represented family; the retained source presentation then yields genuine `AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state`. The polynomial family, sections, raw defect and scale are unchanged in this rank refinement. The ray geometry is the source-honest certificate licensing the repair promotion.

This is exactly the architectural pattern already used for concrete wall-face curvature and for the geometry-gated `AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.ofGeometry` constructor.

## 9. Paper theorem

The intended theorem is therefore:

> **Source-honest other-facet ray closure.** Let `T` be a zero-strict-low singular terminal and `C` a retained lower first-nonfacet `.qs` ray. If the starting endpoint is rank three on `.qs` and the outside endpoint is rank three on any of `.pr`, `.sp`, `.rq`, then there exists a target state with genuine `AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state`.

No auxiliary ray clock occurs in the statement or proof.

Consequently the rank-three other-facet alternative in the locked first-ray frontier is not terminal. The still-live same-carrier codimension-two starting-endpoint alternative is separate.

## 10. Lean implementation checklist

Before adding new algebra, reuse:

* `ray_direct_initialForm_package` for exact source provenance;
* `qs_ray_*_outside_strict_directionLock` for `B*R=C*Q` and strict coordinate drops;
* `qs_ray_degreeOne_supportedLine` plus endpoint coefficient nonvanishing for the two-term line form;
* `qs_ray_transverseHessianMinor_ne_zero` for (5);
* existing cyclic active permutations from `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfaceSchur`;
* the generic B38 negative-square algebra if it can be factored out state-freely;
* the geometry-gated same-family promotion proof from `AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerGeometry`.

Likely genuinely new Lean material:

1. one generic cyclic lemma identifying `schurC` with the principal `3 x 3` minor complementary to coordinate zero;
2. one division-free direction-lock-to-Schur-wedge lemma implementing (1)--(8);
3. one exposed-ray geometry packet/constructor tied to the presented blocker;
4. one short global adapter producing `GlobalMacroProgress` from that packet.

Do not use or identify the positive auxiliary ray Schur clock in this closure theorem.
