# HC4 proof paths

**Route map checkpoint: 12 September 2026.**

This document answers: given the current carrier, which canonical owner should
be used next, what does it produce, and which tempting shortcut must not be
substituted?

For theorem-level status use `CURRENT_STATE.md`. For the mathematical picture
use `PROOF_ARCHITECTURE.md`. For the exact implementation order use
`FORMALISATION_PLAN_2026-09-12.md`.

## 1. Unrestricted front door

| Have | Use | Get | Do not substitute |
|---|---|---|---|
| `F` with `hessianDeterminant F = 1` and a hypothetical distinct exact gradient collision | `AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`, `...CollisionAutoDegree.lean` | normalized collision + canonical degree data | no homogeneous-input assumption; no caller-supplied degree cap |
| normalized exact collision | `AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean` | canonical zero-defect collision entry and positive rank-one re-entry | do not create a parallel entry state |
| collision entry | `AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean` | reachable rank-one terminal obligation with repair provenance | do not quantify over arbitrary unrelated terminals if reachability is available |

**Status: LEAN VERIFIED.**

## 2. Global rank-one termination

| Have | Use | Get | Do not substitute |
|---|---|---|---|
| canonical rank-one state | `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean` | recursion on actual `rawDefect : Nat` | no rational/cross-scale well-founded recursion |
| successful positive Rees bound at actual trace state | `...PositiveTransverseReesSourceProgress.lean`, `...RankOneReesTraceReduction.lean` | existing restart edge with global progress + raw-defect drop + repair equality | do not measure only after a presentation/ramification |
| reached rank-three state | `...RankOneReesRankThreeClosure.lean` | outer global successor or literal `rawDefect = 0` | do not leave positive reached geometry as final local TODO |
| completed trace | `...RankOneTraceCollapse.lean` | contradiction once local terminal impossibility is supplied | do not invent a second final trace |

**Status: LEAN VERIFIED.**

## 3. Local zero-clock entry

```text
reached globally terminal rank-three state
        |
        v
rawDefect = 0
        |
        v
producer-free zero strict-low terminal
        |
        v
singular maximal ordinary top face
        |
        v
A19.55 boundary split
```

Canonical chain:

```text
A19.49  residual normal form
A19.50  same-exponent mixed degree
A19.51  zero-clock packet
A19.52  honest first-contact Hessian geometry
A19.53  producer-free zero strict-low terminal
A19.54  singular maximal ordinary top face
A19.55  balance-free boundary rank split
A19.56+ retained boundary/source provenance
```

**Status: LEAN VERIFIED up to the A19.55 split.**

## 4. A19.55 rank-three other-facet route

### Have

An actual rank-three boundary exponent/carrier with retained source/contact
provenance, eventually yielding the locked source ray in the surviving
other-facet branch.

### Use next — paper route

```text
locked source ray
        |
        v
defect-neutral source exposure
        |
        v
exact singular planar carrier
        |
        v
highest pair-degree singular slice
        |
        v
line-supported Hessian rigidity
        |
        v
primitive two-monomial slice(s)
        |
        +------------------------------+
        |                              |
        | non-singleton fibers         | singleton/developable escape
        v                              v
two-function full Hessian        contact/top-degree classification
factorisation contradiction      contradiction
        |                              |
        +------------------------------+
                       |
                       v
                 branch impossible
```

### Canonical existing owners to reuse

- finite support/exposure/ray infrastructure under `HC4/Newton/`;
- `fourOrdinaryDegreeComponent` owner in
  `AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer.lean`;
- exact initial-form/Hessian identities;
- source/contact support provenance already retained by A19.66--A19.73;
- `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` for the paper recurrence.

### New formal obligations

1. source-honest defect-neutral planar refinement;
2. highest pair-degree Hessian singularity adapter;
3. Lean line-supported rigidity theorem;
4. full two-function Hessian factorisation/contradiction;
5. tailored singleton/developable elimination;
6. separate `V=1` mixed-orientation coefficient elimination.

### Do not substitute

- do not identify the auxiliary ray defect with the zero blocker;
- do not infer superface singularity from the ray alone;
- do not call the four-monomial cross-ratio relation a contradiction;
- do not collapse to generic JC2 merely because a two-zero projection exists.

**Status: PAPER CANDIDATE.**

## 5. A19.55 same-carrier codimension-two route

### Important identity

This is the earlier top-face/same-carrier codimension-two branch. It is **not**
the later degree-one lower `.qs` outside endpoint already eliminated elsewhere.

### Paper route

```text
codimension-two top vertex
+ two independent first departures
        |
        v
extremal Hessian coefficient
        |
        v
m=1 or n=1
        |
        v
next extremal coefficients
        |
        +-------------------+----------------------+
        |                   |                      |
        v                   v                      v
nonzero 2x2 minor   all-minors-zero rigid   constant-kernel cone
                                                   |
                                                   v
                                      ordinary reverse-Rees family
                                                   |
                                                   v
                                      first kernel-breaking layer q
                                                   |
                                                   v
                                      q < determinant closure
                                                   |
                                                   v
                                  filtered first-kernel-break lemma
                                                   |
                                                   v
                                      explicit `-(H_i3)^2 != 0`
```

### Primitive-departure coefficient package

Use the normalization

```text
H0 = x^p y^(D-p)
Hz = A x^a y^(D-m-a) z^m
Hw = B x^c y^(D-n-c) w^n.
```

First coefficient:

```text
-A*B*p*(D-p)*m*n*(m-1)*(n-1)*(D-1).
```

Hence `m=1` or `n=1`.

Next cases:

- `m=n=1` gives `(a-c)^2=0`, hence a single transverse linear form and a
  constant shear;
- `m=1<n` gives `a=0` or `a=D-1`, then respectively `(p,c)=(1,0)` or
  `(D-1,D-n)`, again a constant-kernel shear;
- `n=1<m` is symmetric.

### New generic algebra owner

`docs/FILTERED_FIRST_KERNEL_BREAK_LEMMA.md` is the paper specification.
Planned Lean file:

```text
HC4/Valuation/FirstKernelBreakRankTwo.lean
```

It should consume only a polynomial family, a rank-three special kernel,
`q < Delta`, and the first kernel-break condition.

### Ordinary reverse-Rees owner

Planned Lean file:

```text
HC4/Valuation/FourOrdinaryReverseRees.lean
```

Reuse the existing `fourOrdinaryDegreeComponent`; do not create another
ordinary-degree API.

Required identities:

```text
R_F(t,x)=sum t^q H_(D-q)(x)=t^D F(x/t)

det Hess(R_F)=t^(4D-8)

familyParameterLayer R_F q = H_(D-q)

grad F(a)=grad F(b)
  -> grad R_F(t,t*a)=grad R_F(t,t*b)
```

If `q` is the first layer breaking the top constant kernel,

```text
q <= D-2 < 4(D-2),
```

so the kernel break is strictly preclosing.

### Existing consumers

Use existing geometry-bearing rank-two interfaces only after producing the
actual nonzero Hessian minor. In particular, the first-key transverse rank
frontier already stores a concrete nonzero `2 x 2` minor before attaching the
canonical rank-one -> rank-two repair step.

### Do not substitute

- no generic JC2 projection;
- no naked `withRepairOnly` contradiction;
- no identification of ordinary reverse-Rees order with a blocker/ray clock.

**Status: PAPER CANDIDATE.**

## 6. Existing source/Hessian coefficient bridge

For any polynomial family `P`, the repository already proves

```lean
familyParameterHessianLayer P n =
  HC4.Polynomial.hessian (familyParameterLayer P n)
```

and zero Hessian layers below the first actual positive source order.

Owner:

```text
AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge.lean
```

Reuse it in `FirstKernelBreakRankTwo.lean`.

**Status: LEAN VERIFIED.**

## 7. Existing geometry-bearing rank-two exits

Canonical examples already present:

- nonzero mixed wall-face Hessian determinant;
- nonzero base-plane Hessian determinant;
- moving raw Schur derivative packet;
- first-key transverse Hessian minor;
- moving cleared-lift derivative block.

Owner examples:

```text
AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry.lean
AdaptiveAlignedSmithRankOneSchurFirstKeyTransverseRankFrontier.lean
AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRS2LiftRepair.lean
```

These files establish the required architectural direction:

```text
actual source geometry
        ->
canonical rank-two transition
```

never the reverse.

## 8. Historical ray-Schur route

The `.pr` auxiliary ray Schur clock, constant minor, weight bounds and exact
clock mismatch remain valid proved infrastructure. Their important lesson is
negative as well as positive:

```text
ray clock != original zero blocker clock.
```

They are therefore not the direct terminal contradiction route. Keep them as
local tools/historical milestones rather than resurrecting an invalid direct
stationary splice.

## 9. JC2 modules

The generic two-zero/JC2 infrastructure remains useful and proved where its
hypotheses are genuinely available. It is not the live unrestricted closure
route because both current A19.55 branches retain stronger provenance and have
a paper route that closes before generic JC2.

Do not delete the JC2 modules; just do not use them as an unproved adapter.

## 10. Formalisation order

Use exactly this sequence unless a compile failure exposes a better reuse
point:

```text
1. FirstKernelBreakRankTwo.lean
2. FourOrdinaryReverseRees.lean
3. A19 codim-two primitive-departure theorem
4. A19 codim-two closure/splice
5. defect-neutral planar refinement
6. highest-slice adapter
7. line-supported rigidity in Lean
8. rank-three carrier/singleton closure
9. eliminate both A19.55 constructors
10. invoke reachable-terminal HC4 reduction
11. full root build + axiom audits
```

Detailed theorem decomposition is in `FORMALISATION_PLAN_2026-09-12.md`.

## 11. Completion condition

Do not claim unrestricted HC4 from the paper closure alone. The route is
complete only when the public determinant-one gradient injectivity theorem is
Lean verified with no caller-supplied resolver, balance/homogeneity assumption,
JC2 hypothesis, clock conflation, or repair-only contradiction, and the audited
root build is green.
