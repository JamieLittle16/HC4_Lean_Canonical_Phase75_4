# Current HC4 Lean proof state

**Authoritative status checkpoint: 12 September 2026.**

This document owns theorem-level status for the live unrestricted HC4 final
assembly. It deliberately distinguishes:

- **LEAN VERIFIED** — already formalised and compiled in the repository;
- **PAPER CANDIDATE** — a complete paper argument is currently available but
  has not yet been formalised and may still fail under formal scrutiny;
- **OPEN** — a genuine mathematical or formal interface obligation remains.

For the mathematical architecture see `PROOF_ARCHITECTURE.md`. For the exact
implementation order see `FORMALISATION_PLAN_2026-09-12.md`. The new elementary
kernel-break theorem is written out in `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`.
Older handoffs and ray-clock notes remain historical evidence and are not the
current TODO list.

## 1. Public target

The unrestricted target is determinant-one gradient injectivity in four
variables:

```lean
F : MvPolynomial (Fin 4) K
hdet : HC4.Polynomial.hessianDeterminant F = 1
⊢ Function.Injective (mvGradientMap F)
```

under the A19 ambient assumptions. The public input is not assumed homogeneous,
torus-balanced, pre-normalised, or equipped with a caller-supplied degree cap.

**Status: LEAN VERIFIED for the unrestricted entry/reduction interfaces; not yet
LEAN VERIFIED for the final unconditional HC4 theorem.**

## 2. Global architecture already complete in Lean

The following are not live research gaps:

1. exact collision normalisation;
2. automatic nonlinear degree cap;
3. canonical zero-defect entry;
4. the rank-one raw-defect termination trace;
5. positive Rees restart edges at actual trace states;
6. collapse of positive reached rank-three terminal geometry to literal
   raw defect zero;
7. producer-free zero-clock strict-low terminal data;
8. retention of canonical repair/source provenance through the terminal path.

The rank-one recursion remains the existing natural-number recursion on actual
`rawDefect`. Do not introduce a second rational clock, cross-scale recursion,
or repair-rank termination order.

**Status: LEAN VERIFIED.**

## 3. The live zero-clock strict-low frontier

The Lean path reaches an actual represented zero-clock strict-low source and
retains a genuine singular maximal ordinary homogeneous top face. A19.55 gives
the exhaustive balance-free boundary split

```text
rank three on a coordinate facet
OR
same-carrier codimension two.
```

These two branches must remain separate. The later theorem eliminating a
particular degree-one lower `.qs` outside endpoint from codimension two does
not eliminate the earlier A19.55 same-carrier/top-face codimension-two branch.

**Status: LEAN VERIFIED up to the split.**

## 4. Rank-three other-facet branch

### 4.1 Source-honest defect-neutral planar refinement

Starting from the locked source ray with positive Hessian defect, use the
neutral perturbation

```text
u = (1,1,0,0),
(W_t,L_t) = (W+t*u,L+t).
```

The defect is exactly preserved:

```text
4(L+t) - 2*sum(W+t*u) = 4L - 2*sum W.
```

A small independent neutral skew perturbation chooses a generic first normal
fan wall, giving an exact source planar carrier that contains the locked ray
and genuine nonlinear support while retaining positive determinant defect.
Singularity comes from the exact source exposure, not by inheriting singularity
from a smaller face.

**Status: PAPER CANDIDATE.**

### 4.2 Highest-slice singularity

Grade the planar carrier by pair degree `p=e0+e1`. Every `4 x 4` Hessian
determinant monomial loses exactly four units of this grading. If `N` is the
maximal occupied pair degree, then

```text
[degree_p = 4*N-4] det Hess(G) = det Hess(G_N).
```

Hence the highest slice is singular.

**Status: PAPER CANDIDATE.**

### 4.3 Line-supported rigidity

For a finite line-supported singular-Hessian polynomial in direction

```text
(1,-1,-alpha,-beta),
```

the completed one-variable recurrence/rational-first-integral argument forces
any nonconstant slice to consist of two adjacent monomials. For `V>1` the
primitive direction is uniquely

```text
(1,-1,-1,-V).
```

The paper derivation is owned by
`LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`.

**Status: PAPER CANDIDATE.**

### 4.4 Two-function carrier is impossible

If singleton fibers are absent, the `V>1` carrier has the form

```text
F = x(Q(Y)+b H^ell) + z(P(Y)+a H^ell Y),
Y = y w^V,
H = z w^V.
```

The full Hessian determinant factors as

```text
V*ell*(V+1)*w^(V*ell+2*V-2)*z^(ell-2) * A * B,
```

where

```text
A = Y(x Q' + z P') + H^ell(b*ell*x + a*(ell+1)*z*Y)
```

and

```text
B = x( b(ell-1)(Q')^2 + b^2*ell*H^ell*Q'' )
  + z( a(ell+1)Y(Q')^2 - 2bP'Q'
       - 2ab(ell+1)H^ell Q' + b^2*ell*H^ell P'' ).
```

The locked lower ray makes `A != 0`. A primitive nonlinear slice has `Q' != 0`.
`B=0` first forces `ell=1` and `Q''=0`; then it forces simultaneously

```text
P'  = (a Q'/b) Y,
P'' = 4 a Q'/b,
```

whereas differentiating the first identity gives `P'' = a Q'/b`. This is
impossible in characteristic zero.

The older four-monomial cross-ratio equation is only one exact coefficient
constraint and is **not** a contradiction by itself.

**Status: PAPER CANDIDATE.**

### 4.5 Singleton/developable escape

Bare Hessian singularity does allow developable singleton staircases, so this
step must use retained A19 contact/source provenance. After the `(X,Y,H)`
substitution, the contact inequality determines the unique top ordinary
homogeneous term

```text
R_(ell+2) = A * Y * H^(ell+1).
```

The characteristic-zero small-dimensional singular-Hessian classification
(de Bondt--van den Essen, *Singular Hessians*, J. Algebra 282 (2004), 195--204)
then leaves a constant-kernel alternative or a developable
`g(L)+M p(L)+N q(L)` alternative. The top term and contact bound eliminate
both: a constant kernel is forced into the `X` direction but the locked ray
contains `X H^ell`; in the developable case divisibility of the top piece
forces `L ~ H`, which makes every nonlinear monomial have pair degree at most
one, contradicting the retained strict planar support with pair degree `>1`.

For Lean, prefer a tailored A19 proof over formalising the entire published
classification if possible.

**Status: PAPER CANDIDATE.**

### 4.6 `V=1`

Keep the symmetric case separate. Same-orientation carriers are killed by the
same full determinant factorisation. Mixed orientations are killed by extremal
coefficient equations ending in

```text
2 AD = BC,
AD = 2 BC,
```

with all four endpoint coefficients nonzero.

**Status: PAPER CANDIDATE.**

### Rank-three branch conclusion

No generic JC2 projection is needed on the current paper route.

**Status: PAPER CANDIDATE — no known paper-local subbranch remains, but Lean
formalisation may expose missing hypotheses.**

## 5. Same-carrier codimension-two branch

This is the A19.55 branch, not the later already-eliminated degree-one lower
endpoint case.

### 5.1 Primitive departures force a cone

Normalise a codimension-two homogeneous vertex and two independent first
departures as

```text
H0 = x^p y^(D-p),
Hz = A x^a y^(D-m-a) z^m,
Hw = B x^c y^(D-n-c) w^n.
```

The extremal Hessian coefficient is, up to nonzero active factors,

```text
-A*B*p*(D-p)*m*n*(m-1)*(n-1)*(D-1).
```

Thus `m=1` or `n=1`.

If `m=n=1`, the next surviving coefficient is

```text
A^2 * B^2 * (D-1)^2 * (a-c)^2,
```

so `a=c`, and a constant transverse shear combines the departures into a
single linear form and removes one coordinate.

If `m=1<n`, the next channels force `a=0` or `a=D-1`. In the first case they
then force `(p,c)=(1,0)`; in the second they force `(p,c)=(D-1,D-n)`. Both
normal forms again admit an explicit collision-preserving constant shear to a
literal constant coordinate kernel. The case `n=1<m` is symmetric.

Thus the primitive-departure branch is not generic two-zero JC2 geometry: it
is forced to an explicit constant-kernel cone, unless rank-two Hessian geometry
is already visible.

**Status: PAPER CANDIDATE.**

### 5.2 Filtered first-kernel-break theorem

The precise theorem is owned by `FILTERED_FIRST_KERNEL_BREAK_LEMMA.md`.

For a family

```text
P(t,x) = sum t^n P_n(x),
det Hess(P) = t^Delta,
```

suppose the special Hessian has literal kernel coordinate `3` and nonzero
complementary `3 x 3` determinant. Let `q` be the first order breaking that
kernel and suppose `0 < q < Delta`. Then the order-`q` determinant coefficient
is exactly

```text
activeThreeDet * Hess(P_q) 3 3.
```

Hence `Hess(P_q) 3 3 = 0`. Since `P_q` does break the kernel, some mixed entry
`Hess(P_q) i 3` is nonzero, and therefore the actual source layer contains

```text
H_ii * H_33 - H_i3 * H_3i = -(H_i3)^2 != 0.
```

This is honest rank-two Hessian geometry, not a repair tag.

**Status: PAPER CANDIDATE.**

### 5.3 Ordinary reverse-Rees adapter

For the actual represented source

```text
F = sum H_m,
```

with maximal ordinary degree `D >= 3`, use

```text
R_F(t,x) = sum_{q=0}^D t^q H_(D-q)(x) = t^D F(x/t).
```

Then

```text
det Hess(R_F) = t^(4D-8).
```

If `grad F(a)=grad F(b)`, the sections `t*a` and `t*b` retain an exact moving
collision. If the top homogeneous kernel is eventually broken, choose the
first breaking index `q`. Since a component of degree at most one has zero
Hessian,

```text
q <= D-2 < 4(D-2) = 4D-8.
```

Thus the filtered first-kernel-break theorem applies strictly before closure
and produces the nonzero minor on an actual homogeneous source layer.

This reverse-Rees clock is independent of the zero blocker and of the earlier
auxiliary ray clock.

**Status: PAPER CANDIDATE.**

### Codimension-two branch conclusion

The branch reaches one of:

```text
immediate nonzero 2 x 2 Hessian minor
OR
existing all-minors-zero rigid / linear-power branch
OR
constant-kernel rank-three cone -> reverse Rees -> nonzero 2 x 2 minor.
```

No generic JC2 fallback is required on the current paper route.

**Status: PAPER CANDIDATE — no known paper-local subbranch remains.**

## 6. Existing Lean consumers for the new geometry

The repository already has the source/Hessian coefficient bridge

```lean
familyParameterHessianLayer_eq_hessian
```

and geometry-bearing rank-two consumers. In particular, the first-key
transverse rank frontier stores an actual nonzero `2 x 2` Hessian minor before
attaching canonical rank-one-to-rank-two progress.

Likewise the residual global geometry interface only attaches progress after
one of a finite list of real Hessian/Schur witnesses has been supplied.

**Status: LEAN VERIFIED.**

## 7. What remains open now

### Mathematics

No specific local mathematical branch from the 12 September audit is currently
known to remain open. This is **not** a claim that HC4 is proved: every new
closure above is still only `PAPER CANDIDATE` and may reveal a gap under Lean
formalisation or independent review.

### Formalisation

The live work is:

1. formalise the generic filtered first-kernel-break lemma;
2. formalise the ordinary reverse-Rees family and collision/determinant
   identities;
3. formalise the A19.55 codimension-two primitive-departure cone theorem;
4. splice that branch into existing geometry-bearing rank-two consumers;
5. formalise the rank-three planar refinement/highest-slice/line-rigidity and
   singleton/developable closure;
6. eliminate both residual terminal constructors;
7. invoke the already-existing reachable-terminal HC4 reduction;
8. compile the public unrestricted theorem and run the full proof/axiom audits.

The exact file order is in `FORMALISATION_PLAN_2026-09-12.md`.

## 8. Hard prohibitions carried forward

Do not:

- identify an auxiliary Rees clock with the zero blocker;
- treat naked `withRepairOnly` progress as a contradiction;
- infer singularity of a superface merely from singularity of a smaller ray;
- collapse the A19.55 codimension-two branch to generic JC2 without proving the
  additional adapter hypotheses;
- use the four-monomial cross-ratio equation as a contradiction by itself;
- conflate the A19.55 codimension-two branch with the later A19.91 lower
  endpoint codimension-two elimination;
- add a second rank-one recursion.

## 9. Completion criterion

Unrestricted HC4 is reached only when the top-level determinant-one gradient
injectivity theorem is Lean verified with no caller-supplied resolver,
producer, terminal-impossibility hypothesis, balance assumption, homogeneity
assumption, or JC2 hypothesis, and the audited root build is green.

**Current description:** unrestricted entry and global termination are Lean
built; the final local mathematics has a complete paper candidate; formalising
that paper closure and performing the final splice is the remaining task.
