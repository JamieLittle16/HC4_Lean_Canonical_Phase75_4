# HC4 proof architecture

**Architecture checkpoint: 12 September 2026.**

This document explains the live unrestricted HC4 proof architecture by proof
role. It is not a chronological phase diary.

Documentation ownership:

- `CURRENT_STATE.md` — authoritative theorem/status ledger;
- `PROOF_ARCHITECTURE.md` — this file, mathematical architecture;
- `PROOF_PATHS.md` — route map from current carriers to canonical owners;
- `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md` — precise new algebraic lemma;
- `FORMALISATION_PLAN_2026-09-12.md` — implementation order;
- `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` — line-rigidity paper proof;
- `CANONICAL_OWNERS.md` — reusable theorem/definition ownership;
- `GLOSSARY_AND_INVARIANTS.md` — vocabulary and provenance rules;
- `HISTORICAL_AND_SUPERSEDED_ROUTES.md` — older routes and why they are no
  longer the live TODO list;
- `generated/LEAN_MODULE_INDEX.md` and `generated/DECLARATION_INDEX.md` —
  exhaustive Lean inventory.

Use the status labels `LEAN VERIFIED`, `PAPER CANDIDATE`, and `OPEN` exactly as
defined in `CURRENT_STATE.md`.

## 1. Top-level proof shape

```text
F with det Hess(F)=1
+ hypothetical distinct gradient collision
        |
        v
canonical collision normalisation
+ automatic nonlinear degree cap
        |
        v
zero-defect collision entry
        |
        v
canonical positive rank-one re-entry
        |
        v
existing rawDefect termination trace
        |
        v
actual reached rank-three state
        |
        +------------------------------------------+
        |                                          |
        | outer global successor                   | globally terminal
        v                                          v
continue existing trace                     rawDefect = 0
                                                   |
                                                   v
                                      zero-clock strict-low source
                                                   |
                                                   v
                                      singular maximal top face
                                                   |
                                                   v
                                  A19.55 balance-free boundary split
                                                   |
                          +------------------------+-----------------------+
                          |                                                |
                          v                                                v
                 rank-three facet / other facet              same-carrier codim two
                          |                                                |
                          v                                                v
              source-honest planar closure                 primitive departures
                          |                                                |
                          v                                                v
               line rigidity + contact                    constant-kernel cone
                / singleton elimination                           |
                          |                                      v
                          |                           ordinary reverse-Rees
                          |                                      |
                          |                                      v
                          |                           first kernel-breaking layer
                          |                                      |
                          |                                      v
                          |                           nonzero 2x2 Hessian minor
                          |                                      |
                          +----------------------+---------------+
                                                 |
                                                 v
                                  existing geometry-bearing consumers
                                                 |
                                                 v
                                    existing global trace/descent
                                                 |
                                                 v
                                reachable-terminal HC4 contradiction
```

The upper half of this diagram is already formalised. The two lower local
closure paths are the current **PAPER CANDIDATE** mathematics to formalise.

## 2. Unrestricted entry and global termination

The public theorem does not assume homogeneity, balance, a degree cap, or JC2.
The canonical collision normalisation and automatic degree selection already
enter the scale-aware state machine.

The only rank-one recursive object is the existing termination trace, whose
recursive measure is the natural number `rawDefect`. Successful positive Rees
moves at actual trace states are ordinary restart edges when they supply
existing global progress, strict actual raw-defect decrease, and unchanged
repair provenance.

Architectural prohibition: do not introduce rational well-founded descent,
cross-scale descent treated as a natural order, repair promotion as a new
termination measure, or a parallel final trace.

**Status: LEAN VERIFIED.**

## 3. Global/local boundary

The decisive global theorem forces any reached rank-three state that is
terminal for the outer global macro order to have literal raw defect zero.
Therefore positive reached rank-three geometry is not a final local branch.

The local proof begins from the producer-free zero-clock strict-low terminal,
retaining the actual represented source, the canonical repair equality, and
the strict-low Smith pattern.

**Status: LEAN VERIFIED.**

## 4. A19.55 is the only local boundary split to close

The singular maximal ordinary top face exposes an actual nonlinear boundary
exponent and splits exhaustively into

```text
rank three on a coordinate facet
OR
same-carrier codimension two.
```

The codimension-two constructor here is not the later degree-one lower `.qs`
outside endpoint that A19.91 eliminates. Keep them distinct.

The final proof should eliminate both A19.55 constructors without adding a
caller-supplied resolver.

**Status: LEAN VERIFIED up to this split.**

## 5. Rank-three other-facet architecture

### 5.1 Exact source ray, not an auxiliary terminal clock

The rank-three route retains an actual source-supported locked ray and actual
contact provenance. Auxiliary ray-Rees clocks may be useful local calculations,
but they are not the zero blocker clock and must not be fed directly into a
stationary terminal contradiction.

The current paper route instead stays source-honest.

### 5.2 Defect-neutral planar refinement

Let `(W,L)` expose the locked ray and have positive Hessian defect. Perturb by

```text
u = (1,1,0,0),
(W_t,L_t)=(W+t*u,L+t).
```

The determinant defect is invariant:

```text
4(L+t)-2*sum(W+t*u)=4L-2*sum W.
```

A small independent neutral skew perturbation selects a generic first
normal-fan wall. Finite support lets us keep source weights positive and choose
an exact rational, hence integral, exposure. The new planar carrier contains
the ray and genuine nonlinear source support and is singular because it is an
exact positive-defect source exposure.

Do not infer this singularity from the smaller ray.

**Status: PAPER CANDIDATE.**

### 5.3 Highest pair-degree slice

Grade by `p=e0+e1`. A `4 x 4` Hessian determinant loses exactly four units of
pair degree. For maximal occupied pair degree `N`,

```text
[degree_p = 4*N-4] det Hess(G) = det Hess(G_N).
```

Thus the highest slice is itself singular. Since the planar carrier contains
the ray direction and that direction has pair degree zero, a nonconstant
highest slice lies on an affine line parallel to the locked ray.

**Status: PAPER CANDIDATE.**

### 5.4 Line-supported rigidity

The one-variable recurrence/rational-first-integral theorem in
`LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` says that a nonconstant finite
line-supported singular-Hessian polynomial in direction

```text
(1,-1,-alpha,-beta)
```

has only two adjacent monomials. For `V>1`, the primitive orientation is
uniquely

```text
(1,-1,-1,-V).
```

**Status: PAPER CANDIDATE.**

### 5.5 Non-singleton carrier contradiction

If all nonlinear quotient fibers are nonconstant, the carrier takes the form

```text
F=x(Q(Y)+b H^ell)+z(P(Y)+a H^ell Y),
Y=y w^V,
H=z w^V.
```

Its full Hessian determinant factors as

```text
V*ell*(V+1)*w^(V*ell+2*V-2)*z^(ell-2) * A * B
```

with the explicit factors recorded in `CURRENT_STATE.md` and the formalisation
plan. The locked lower ray makes `A != 0`; a primitive top slice has `Q' != 0`.
The equations `B=0` force `ell=1`, `Q''=0`, and inconsistent formulas for
`P''`.

This is the actual contradiction. The older four-monomial cross-ratio equation
is only one coefficient relation and must never be cited alone.

**Status: PAPER CANDIDATE.**

### 5.6 Singleton/developable escape

Bare singular-Hessian geometry admits developable staircase families, so the
proof must spend the retained A19 contact/source provenance.

After the `(X,Y,H)` substitution, the contact inequality pins the unique top
ordinary homogeneous piece to

```text
A * Y * H^(ell+1).
```

The characteristic-zero three-variable singular-Hessian classification then
leaves a constant-kernel or developable normal form. The locked ray and the
contact pair-degree bound rule out both.

For Lean, prefer a tailored proof of this A19-special normal form. Formalising
the full external classification is a fallback.

**Status: PAPER CANDIDATE.**

### 5.7 `V=1`

Keep the symmetric orientation case separate. Same-orientation carriers are
killed by the same determinant factorisation; mixed orientations are killed by
extremal coefficients yielding the incompatible nonzero-endpoint equations

```text
2 AD = BC,
AD = 2 BC.
```

**Status: PAPER CANDIDATE.**

## 6. Same-carrier codimension-two architecture

Do not project this branch to generic two-zero JC2. Its source/contact/ray
provenance gives a stronger finite route.

### 6.1 Primitive departures

Normalise the codimension-two top vertex and two independent departures as

```text
H0 = x^p y^(D-p)
Hz = A x^a y^(D-m-a) z^m
Hw = B x^c y^(D-n-c) w^n.
```

The first extremal determinant equation forces `m=1` or `n=1`.

The next equations close every case:

- `m=n=1` forces `a=c`, so the two departures share one transverse linear
  form and a constant shear removes the complementary coordinate;
- `m=1<n` forces `a=0` or `a=D-1`, then respectively
  `(p,c)=(1,0)` or `(D-1,D-n)`, again giving an explicit constant-kernel
  shear;
- `n=1<m` is symmetric.

Thus the branch reaches an immediate rank-two witness, an all-minors-zero
rigid residual, or a literal constant-kernel cone.

**Status: PAPER CANDIDATE.**

### 6.2 Filtered kernel break

The constant-kernel rank-three case is consumed by the standalone theorem in
`FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`.

For a polynomial family with

```text
det Hess(P) = t^Delta
```

and special Hessian kernel `e3`, let `q` be the first order where that kernel
breaks. If `q < Delta`, the coefficient of `t^q` in the determinant is exactly

```text
activeThreeDet * Hess(P_q) 3 3.
```

Therefore the diagonal kernel entry of `Hess(P_q)` is zero. Since the kernel
breaks, some mixed entry is nonzero, and the corresponding principal minor is

```text
-(Hess(P_q) i 3)^2 != 0.
```

This is an actual polynomial rank-two witness.

**Status: PAPER CANDIDATE.**

### 6.3 Ordinary reverse-Rees is the source-honest adapter

For the represented source with maximal ordinary degree `D`, define

```text
R_F(t,x)=sum t^q H_(D-q)(x)=t^D F(x/t).
```

Then

```text
det Hess(R_F)=t^(4D-8).
```

A gradient collision `a != b` is transported to the exact moving collision
`t*a != t*b` over the polynomial parameter. If `q` is the first homogeneous
layer breaking the constant kernel, then

```text
q <= D-2 < 4(D-2).
```

Thus the first break occurs strictly before closure and the generic filtered
kernel-break theorem gives a nonzero `2 x 2` Hessian minor.

This filtration parameter is separate from every A19 zero/ray/ramification
clock.

**Status: PAPER CANDIDATE.**

## 7. Geometry must precede progress

The repository already contains geometry-bearing consumers for nonzero Hessian
minors, moving Schur wedges, constant source kernels and derivative-lift
rank-two witnesses.

The final adapters must produce one of these geometric objects first. Only
then may existing finite repair/global progress machinery be invoked.

A naked `withRepairOnly` successor, a smaller repair tag, or a semantic rank
promotion is not itself a contradiction.

**Status: LEAN VERIFIED infrastructure.**

## 8. Why generic JC2 is no longer the active plan

The unrestricted generic two-zero projection is indeed full JC2 and cannot be
used as a casual terminal lemma. The current branches retain much stronger
source/contact provenance:

- the rank-three branch retains a locked ray, exact positive source exposure,
  contact-face bounds and primitive line slices;
- the codimension-two branch retains a concrete top carrier and first
  departures that force a constant-kernel cone before any generic planar
  projection.

Therefore the current paper programme closes both branches before generic JC2.
The JC2 modules remain valid reusable/historical infrastructure but are not the
preferred unrestricted final splice.

## 9. Provenance invariants

Keep distinct until a theorem explicitly identifies them:

```text
original source
normalised/recentered source
polynomial family
family special fibre
presented/ramified family
blocker special fibre
right-recentered special fibre
maximal ordinary top face
first-contact face
lower first-nonfacet carrier
finite-support ray
neutral planar refinement
ordinary reverse-Rees family
```

Likewise keep distinct:

```text
source raw defect
presented raw defect
endpoint defect
zero blocker clock
ray-Rees defect
parameter-layer order
ordinary reverse-Rees order
ramified parameter order
```

No equality between these quantities may be inserted merely because their
roles look analogous.

## 10. What not to rebuild

Search existing owners before creating:

- ordinary degree components;
- weighted initial forms and support identities;
- finite-support exposed vertices/rays;
- family parameter layers and Hessian coefficient extraction;
- source-coordinate kernel transport;
- Schur projective wedges;
- rank-two Hessian witness structures;
- geometry-bearing global progress;
- rank-one termination recursion.

The formalisation plan lists the genuinely new modules.

## 11. Completion criterion

The paper programme is currently **PAPER CANDIDATE closed**: no specific local
branch from the 12 September audit is known to remain unresolved.

That is not yet unrestricted HC4. Completion requires Lean verification of the
new local lemmas and adapters, elimination of both A19.55 constructors, and a
green audited public theorem proving determinant-one gradient injectivity with
no caller-supplied resolver, producer, balance assumption, homogeneity
assumption, or JC2 hypothesis.
