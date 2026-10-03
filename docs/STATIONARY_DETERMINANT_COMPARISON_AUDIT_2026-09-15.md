# Stationary determinant comparison audit — 15 September 2026

Base head: `2bc3abfd7fac4e275e0754964f0365521a1bb983`.
This audit follows Commit A of the final-closure handoff.

## What the comparison must additionally prove

The handoff correctly warns that the raw pair-sheared source Hessian is not
the canonical profile Hessian. Retaining the falling-Euler correction does
not, by itself, make the proposed determinant implication valid.

Take `V=2`, `ell=4`, `n=3`. Then the stationary weight is `r=6`, total
stationary degree is `12`, and the honest monomial family

```
Q(tau,x,y,z,w) = tau^6 y^2 z^3 w^8
```

has depth `m=1`, pair degree `2`, and parameter order `q=6`.
Its exponent satisfies both carrier affine equations:

```
6 e0 + 4 e1 + 2 e2 = 14
2(e0+e1+e2) - e3 = 2.
```

Consequently it satisfies their falling Hessian rows as well as the
stationary weighted parameter/depth Euler equations. Its source Hessian
has determinant zero, because it is independent of `x`.

After dividing the Euler-scaled source Hessian by `Q`, its matrix is

```
[[0,0,0,0], [0,2,6,16], [0,6,6,24], [0,16,24,56]].
```

The active `(2,3)` determinant is `-240`, so the actual active determinant
is the nonzero polynomial `-240 Q^2`. The source-first pivot can be
cancelled; the pair shear still has determinant zero.

But the parameter/depth falling Hessian is

```
Q * [[q(q-1),qm], [qm,m(m-1)]] = Q * [[30,6], [6,0]],
```

and its determinant is `-36 Q^2`, not zero. The corrected raw pair diagonal
also holds exactly: `6^2*2*(2-1) = 30+(6+1)*6 = 72`.

The two source-coordinate Euler relations hold as well:

```
V*q = 2*6 = 6*(8-2*3)
ell*V*m = 4*2*1 = (3-1)*(8-2*2).
```

This is **not a counterexample to the live A19 target or to HC4**. It lacks
the required nonzero locked and highest endpoint pairs. It is a counterexample
to deriving that target solely from the affine/falling Euler rows, source
singularity, and active-pivot nonvanishing. In particular, a nonzero
scalar/monomial comparison using only these identities cannot work.

**OPEN:** produce the additional endpoint/source-dependent argument which
removes the remaining source-direction contributions, or replace the
comparison with a different source-honest contradiction. The missing step
must not be packaged as an assumed profile-determinant vanishing theorem.

## Implemented source additions

- `StationaryDeterminantComparisonObstruction.lean` records the exact rational
  exponent core, the affine/falling rows, the corrected profile rows, and the
  two different determinants.
- `...PlanarContactStationaryProfileOrder.lean` proves
  `stationary_profileIndex_weight_le` and `stationary_profileOrder_add`
  directly from the live stationary profile's support bound. This completes
  the order arithmetic needed by Commit B, independently of the open
  determinant implication. It does not claim the full extraction theorem.

Both additions are source candidates pending their exact-commit CI build.
The polynomial witness and determinants were also checked by exact symbolic
calculation. No existing proof assumptions or terminal interfaces were changed.
