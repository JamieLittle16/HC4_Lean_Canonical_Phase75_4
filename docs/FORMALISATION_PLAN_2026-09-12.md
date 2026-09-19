# HC4 final formalisation plan — 12 September 2026

**Purpose:** convert the current paper-level closure into Lean without
rebuilding existing infrastructure or weakening source provenance.

This document owns the implementation order. Mathematical details for the new
filtered kernel-break argument live in `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`.
The theorem-level status ledger lives in `CURRENT_STATE.md`.

## Status language

Use these labels consistently:

- **LEAN VERIFIED** — compiled theorem/code already present in the repository.
- **PAPER CANDIDATE** — a complete paper argument is currently available, but
  it has not yet been formalised and may still fail under formal scrutiny.
- **OPEN** — a genuine mathematical or formal interface obligation remains.

Do not upgrade `PAPER CANDIDATE` to `LEAN VERIFIED` merely because the argument
looks straightforward.

## 1. What is no longer the problem

Do not reopen the following architectural questions unless a concrete Lean
failure proves the current interfaces insufficient:

- unrestricted collision normalisation;
- automatic nonlinear degree cap;
- rank-one global termination recursion;
- positive Rees restart edges;
- zero-clock strict-low entry;
- generic JC2 projection as a default endpoint;
- a second global recursion or rational well-founded order.

The remaining work is local theorem formalisation and the final splice.

## 2. New generic algebra first

### Planned file

`HC4/Valuation/FirstKernelBreakRankTwo.lean`

### Goal

Formalise the state-free filtered first-kernel-break theorem from
`docs/FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`.

Work over

```lean
P : MvPolynomial (Fin 4) (Polynomial K)
```

and reuse:

- `familyParameterLayer`;
- `familyParameterHessianLayer`;
- `familyParameterHessianLayer_eq_hessian`;
- `HasPolynomialFamilyHessianDefect`.

### Suggested theorem decomposition

1. `lower_kernel_column_coeff_eq_zero`

   Package the hypothesis that column/row `3` vanishes in every parameter
   layer below `q`.

2. `det_coeff_firstKernelBreak`

   Prove

   ```lean
   (HC4.Polynomial.hessianDeterminant P).coeff q =
     activeThreeDet * familyParameterHessianLayer P q 3 3
   ```

   when the special fibre has zero row/column `3` and every positive Hessian
   layer below `q` also has zero row/column `3`.

   Preferred proof: finite `4 x 4` determinant/permutation expansion. A term
   moving coordinate `3` uses one row-3 and one column-3 entry and therefore
   has order at least `2*q`.

3. `firstKernelBreak_diagonal_eq_zero`

   Combine the coefficient identity with `q < Delta` and
   `det Hess(P) = X^Delta`.

4. `firstKernelBreak_has_principal_rankTwo_minor`

   From nonzero kernel breaking and zero `(3,3)` entry, choose `i < 3` with
   `Hq i 3 != 0` and return

   ```lean
   Hq i i * Hq 3 3 - Hq i 3 * Hq 3 i = -(Hq i 3)^2 != 0
   ```

### Acceptance condition

This file must not mention A19, Smith states, repair states, JC2, or an
auxiliary ray clock. It should be a reusable algebraic lemma.

## 3. Ordinary reverse-Rees family

### Planned file

`HC4/Valuation/FourOrdinaryReverseRees.lean`

### Existing owners to reuse

The repository already contains:

- `fourOrdinaryIntegerWeight`;
- `fourOrdinaryDegreeComponent`;
- `fourOrdinaryDegreeComponent_isHomogeneous`;
- `exists_maximal_fourOrdinaryDegreeComponent`.

Do not define a competing ordinary-degree component API.

### Definition

For a polynomial with maximal ordinary degree `D`, define

```text
R_F(t,x) = sum_{q=0}^D t^q H_{D-q}(x)
```

where `H_m = fourOrdinaryDegreeComponent F m`.

### Required lemmas

1. exact parameter layer:

   ```lean
   familyParameterLayer (fourOrdinaryReverseReesFamily F D) q =
     fourOrdinaryDegreeComponent F (D - q)
   ```

   for `q <= D`;

2. special fibre is the top homogeneous piece;

3. evaluation at `t = 1` recovers `F`;

4. spatial differentiation commutes with the family as expected;

5. determinant clock:

   ```lean
   hessianDeterminant F = 1
   -> HasPolynomialFamilyHessianDefect
        (fourOrdinaryReverseReesFamily F D)
        (4 * (D - 2))
   ```

   under `2 <= D`;

6. collision transport:

   if `grad F a = grad F b`, the sections `t*a` and `t*b` give an exact
   moving collision in the reverse-Rees family.

### Non-negotiable provenance rule

This parameter is the ordinary reverse-Rees filtration parameter. Do not
identify `4*(D-2)` with an A19 endpoint defect, zero blocker, ray defect, or
ramification multiple unless a separate theorem explicitly proves such an
identity.

## 4. A19.55 codimension-two primitive-departure theorem

### Planned file

`HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowCodimTwoPrimitiveDeparture.lean`

### Paper target

From the actual A19.55 same-carrier codimension-two top-face packet, derive an
exhaustive source-honest geometric outcome:

```text
actual nonzero 2 x 2 Hessian minor
OR
all-minors-zero rigid / linear-power branch
OR
constant-kernel cone with complementary rank three
```

The paper coefficient calculation uses the local normalisation

```text
H0 = x^p y^(D-p)
Hz = A x^a y^(D-m-a) z^m
Hw = B x^c y^(D-n-c) w^n
```

and the extremal determinant coefficient

```text
- A*B*p*(D-p)*m*n*(m-1)*(n-1)*(D-1).
```

Thus `m = 1` or `n = 1`.

The next channels give:

- `m=n=1`: `(a-c)^2 = 0`, hence the two transverse departures combine into a
  single linear form and a constant shear removes one coordinate;
- `m=1<n`: `a=0` or `a=D-1`; the subsequent coefficients force the endpoint
  cases `(p,c)=(1,0)` or `(D-1,D-n)`, again giving an explicit
  collision-preserving shear to a constant-kernel cone;
- `n=1<m`: symmetric.

### Formalisation policy

Keep the coefficient identities in a small polynomial algebra file if they
are reusable. The A19 adapter should only supply the exact support/exponent
hypotheses and consume the resulting alternatives.

Do not replace this branch by generic two-zero JC2 geometry.

## 5. A19.55 codimension-two closure

### Planned file

`HC4/Valuation/AdaptiveAlignedSmithCanonicalZeroStrictLowCodimTwoClosure.lean`

In the constant-kernel rank-three outcome:

1. build the ordinary reverse-Rees family of the **actual represented source**;
2. choose the least homogeneous layer that breaks the literal constant kernel;
3. prove its index `q` satisfies `q <= D - 2`;
4. infer `q < 4*(D-2)`;
5. invoke `firstKernelBreak_has_principal_rankTwo_minor`;
6. package the returned minor as genuine source geometry;
7. only then invoke an existing geometry-bearing rank-two consumer.

No `withRepairOnly` object is itself a contradiction.

## 6. Rank-three other-facet paper branch

This branch is also **PAPER CANDIDATE**, not yet Lean verified. Keep it
separate from the codimension-two closure.

The paper chain is:

```text
locked source ray
-> defect-neutral exact source planar refinement
-> highest pair-degree singular slice
-> completed line-supported Hessian rigidity
-> primitive slice(s)
-> singleton/developable exclusion from retained contact data
-> contradiction
```

### 6.1 Defect-neutral planar refinement

Use the perturbation direction

```text
u = (1,1,0,0),  (W_t,L_t) = (W+t*u,L+t)
```

so the Hessian defect is exactly unchanged:

```text
4(L+t) - 2*sum(W+t*u) = 4L - 2*sum W.
```

A small independent neutral skew perturbation makes the first normal-fan wall
genuinely planar while retaining positive source weights and exact source
provenance.

### 6.2 Highest-slice singularity

Grade by pair degree `p=e0+e1`. A `4 x 4` Hessian determinant loses exactly
four units of pair degree, so if `N` is maximal then

```text
[degree_p = 4*N-4] det Hess(G) = det Hess(G_N).
```

Hence the highest slice is singular.

### 6.3 Line rigidity

The completed paper theorem for a finite line-supported singular Hessian
polynomial in direction `(1,-1,-alpha,-beta)` forces a nonconstant slice to
have two adjacent monomials. For `V>1` the primitive direction is uniquely

```text
(1,-1,-1,-V).
```

The existing note `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` owns the
one-variable recurrence argument.

### 6.4 Two-function carrier calculation

If the carrier has no singleton escape, it takes the form

```text
F = x(Q(Y)+b H^ell) + z(P(Y)+a H^ell Y),
Y = y w^V,  H = z w^V.
```

The full Hessian determinant factors as

```text
V*ell*(V+1)*w^(V*ell+2*V-2)*z^(ell-2) * A * B
```

with

```text
A = Y(x Q' + z P') + H^ell (b*ell*x + a*(ell+1)*z*Y)
```

and

```text
B = x( b(ell-1)(Q')^2 + b^2*ell*H^ell*Q'' )
  + z( a(ell+1)Y(Q')^2 - 2bP'Q'
       - 2ab(ell+1)H^ell Q' + b^2*ell*H^ell P'' ).
```

`A != 0`. If `Q' != 0`, `B=0` forces `ell=1`, `Q''=0`, then simultaneously

```text
P'  = (a Q'/b) Y,
P'' = 4 a Q'/b,
```

while differentiating the first gives `P'' = a Q'/b`, contradiction in
characteristic zero.

The old four-monomial cross-ratio equation is only one coefficient constraint;
never cite it alone as the contradiction.

### 6.5 Singleton/developable escape

Bare singularity is insufficient: developable ternary carriers exist. The
paper closure uses the retained A19 contact data to identify the top ordinary
homogeneous part after the `(X,Y,H)` substitution and then applies the
small-dimensional characteristic-zero singular-Hessian classification
(de Bondt--van den Essen, *Singular Hessians*, J. Algebra 282 (2004),
195--204). The two possible rank-two behaviours are a constant kernel or a
developable form `g(L)+M p(L)+N q(L)`. The A19 top form/contact bound kills
both alternatives.

For Lean we should first try to prove the **tailored A19 version** directly;
formalising the entire published classification is a fallback, not the first
choice.

### 6.6 V=1

Keep the symmetric/mixed orientation case separate. The no-singleton same
orientation case is killed by the same full determinant factorisation. Mixed
orientations are killed by extremal coefficient equations, ending in the
incompatible pair

```text
2 AD = BC,
AD = 2 BC.
```

## 7. Final local assembly

Once both paper branches are formalised, update the A19 terminal frontier so
that the old split

```text
rank-three other-facet
OR
same-carrier codimension two
```

has no unresolved constructor.

The final local theorem should return only existing global outcomes:

```text
zero defect / contradiction / certified geometry-backed successor
```

according to the current state-machine interface.

Then splice this into the already-existing reachable-terminal HC4 reduction.

## 8. Validation order

For each new module:

1. compile the module alone;
2. compile its immediate import owner;
3. run the generated declaration/module inventory update if required;
4. run the project proof/axiom audits;
5. only after the local chain is green, run the full root build.

Do not wait until the final splice to debug all new modules at once.

## 9. Completion criterion

Paper closure is **not** unrestricted HC4 until the Lean chain is complete.
The formal project is complete only when the public determinant-one gradient
injectivity theorem has no caller-supplied terminal resolver, producer,
balance assumption, homogeneity assumption, JC2 hypothesis, or hidden
repair-only contradiction, and the audited root build is green.
