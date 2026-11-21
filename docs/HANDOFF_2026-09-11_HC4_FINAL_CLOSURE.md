# HC4 final-closure handoff — 11 September 2026

> **Repository:** `JamieLittle16/HC4_Lean_Canonical_Phase75_4`
>
> **Live PR:** #34 — `A18.4.42 collapse final termination frontier`
>
> **Branch:** `final-assembly/a18-4-42-termination-frontier`
>
> **Head when this handoff was written:** `251879f8c851f4bcad9af4283fa48d6f45d60263`
>
> **Status discipline:** this handoff distinguishes **Lean-verified**, **paper candidate**, and **open** claims. Nothing below should be read as an unrestricted HC4 theorem unless it is explicitly labelled Lean-verified and tied into the public front door.

---

## 0. Executive summary

The unrestricted HC4 proof is no longer missing a global architecture. The unrestricted collision entry, canonical degree choice, rank-one recursion, successful Rees restart mechanism, positive reached-rank-three consumption, and zero-clock terminal reduction are already formalized. The live mathematical problem is local: eliminate the producer-free zero-clock strict-low terminal.

The local geometry has also been reduced very far. The current branch reaches a singular maximal ordinary top face, a balance-free coordinate-boundary split, honest cross-facet first-contact carriers, a finite affine ray, and exact source-exposed ray provenance. The `.pr` contact branch has a large amount of verified Schur/profile infrastructure, including a finite two-coefficient terminal consumer. The old direct contact-coefficient route is nevertheless blocked by genuine lower-index bordered/coupling convolutions; this is an actual mathematical obstruction to that proof strategy, not merely a Lean inconvenience.

Two paper routes have therefore been developed:

1. **Source-honest ray Schur closure.** The exact exposed two-term ray has direction-locked cross-Hessian rows, a nonzero raw Schur projective wedge, and an explicit derivative negative-square rank-two source. This should license same-family rank-one-to-rank-two progress without identifying the auxiliary positive ray clock with the original zero blocker clock. This is recorded in `RAY_SOURCE_HONEST_SCHUR_CLOSURE.md` and is not yet Lean-verified.

2. **Defect-neutral planar refinement and line rigidity.** A newer route avoids the contact parameter-convolution problem altogether. Starting from the exact source-exposed locked ray, use Hessian-defect-neutral exponent refinements to freeze the possible nonlinear repair staircase into a static positive-defect singular carrier. The intended second refinement makes the support planar. Fixed pair-degree slices are then one-dimensional lattice lines. The complete one-variable line-supported Hessian recurrence has now been solved on paper: every nonconstant finite singular line profile is affine, hence consists of exactly two adjacent lattice monomials. This is recorded in `LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md` and is also not yet Lean-verified.

The strongest current paper normal form for the highest nonlinear `.pr` slice is, up to swapping the two transverse coordinates,

\[
(0,n,1,Vn),\qquad (1,n-1,0,V(n-1)),\qquad n>1,
\]

while the original locked ray simultaneously sharpens to

\[
(0,1,\ell+1,(\ell+1)V),\qquad (1,0,\ell,\ell V).
\]

The two rays have the same primitive step

\[
d=(1,-1,-1,-V)
\]

and form a lattice parallelogram:

\[
a+w=b+v.
\]

The immediate open paper seam is therefore **finite two-ray compatibility**, not an infinite recurrence and not generic JC2. The next calculation should take the full four-monomial carrier

\[
F=A X^v+B X^w+C X^a+D X^b
\]

with the parallelogram relation above and classify Hessian singularity. The working expectation is that the determinant factors through the unique coefficient cross-ratio mismatch; this has not yet been proved and must not be assumed.

Separately, the **same-carrier codimension-two branch remains open**. It is not automatically subsumed by the `.pr` two-ray analysis.

If these two local seams are closed and formalized, the global proof is essentially assembly: feed terminal impossibility into the existing rank-one trace collapse and then into the already-existing unrestricted HC4 reduction theorem.

---

# Part I — What is already Lean-verified

## 1. Public target and unrestricted entry

The public target is determinant-one gradient injectivity in four variables:

```lean
F : MvPolynomial (Fin 4) K
hdet : HC4.Polynomial.hessianDeterminant F = 1
⊢ Function.Injective (mvGradientMap F)
```

under the field / characteristic-zero / algebraically-closed assumptions used by the A19 front door.

The unrestricted collision entry is already formalized. The canonical path uses:

- `AdaptiveAlignedSmithCanonicalCollisionNormalization.lean`
- `AdaptiveAlignedSmithCanonicalCollisionAutoDegree.lean`
- `AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.lean`
- `AdaptiveAlignedSmithCanonicalHC4Reduction.lean`
- `AdaptiveAlignedSmithCanonicalHC4ReachableTerminalReduction.lean`

The established architecture does **not** require a homogeneous public input, a caller-supplied nonlinear degree cap, or a pre-normalized toric form.

The theorem

```text
gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
```

already gives the unrestricted conclusion once every canonical reachable presented terminal is impossible.

**Consequence:** do not spend time building another HC4 entry theorem. The missing mathematics is terminal closure.

## 2. Rank-one recursion is complete

The sole rank-one recursive object is

- `AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.lean`.

It recurses only on the natural number `source.rawDefect`, with constructors conceptually of the form

```text
terminal geometry
restart globalProgress rawDefect_lt repair_eq tail
```

and is consumed by

- `AdaptiveAlignedSmithCanonicalRankOneTraceCollapse.lean`.

Successful positive transverse Rees steps are already ordinary restart edges in this trace, through

- `AdaptiveAlignedSmithCanonicalPositiveTransverseReesSourceProgress.lean`
- `AdaptiveAlignedSmithCanonicalRankOneReesTraceReduction.lean`.

**Consequence:** do not introduce a second rational clock, cross-scale well-founded order, repair-rank recursion, or parallel termination trace.

## 3. Positive reached rank-three states are already global progress

`AdaptiveAlignedSmithCanonicalRankOneReesRankThreeClosure.lean` (A19.45) proves at an actually reached Rees-reduced rank-three state:

```text
rawDefect = 0
OR
∃ target, AdaptiveAlignedSmithCanonicalGlobalMacroProgress target reachedState
```

Hence a reached rank-three state which is terminal for the outer global macro order has literal raw defect zero.

This is a major simplification. Older descriptions in which positive low layers were treated as final local terminals are obsolete.

## 4. The live local terminal is producer-free zero-clock strict-low

The current local carrier is

- `AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal.lean` (A19.53).

It retains the actual reached state, canonical rank-one repair equality, presented blocker, source raw defect `= 0`, represented strict-low Smith exponent, support membership, and one of the genuine strict-low patterns.

The exact zero-clock packet is already proved in

- `AdaptiveAlignedSmithCanonicalZeroStrictLowZeroClockPacket.lean`.

In particular the relevant presented/blocker defect is literally zero. This is important because later positive auxiliary Rees clocks must **not** be identified with this blocker clock.

## 5. Verified local geometric path through A19.73

The current zero-strict-low path is already substantial:

```text
A19.49  residual normal form
A19.50  exact same-exponent mixed degree
A19.51  zero-clock packet
A19.52  honest spatial/longitudinal first-departure Hessian geometry
A19.53  producer-free zero strict-low terminal
A19.54  singular maximal ordinary top face
A19.55  balance-free boundary rank split
A19.56  actual finite-support boundary strata
A19.57  recentered positive longitudinal support
A19.58  rank-three top-face cross-facet/confinement split
A19.59  source-level first-nonfacet hypotheses
A19.60  direct-cross / lower-outside / confined source split
A19.61  low-negative actual source support
A19.62  low-negative confinement facet elimination
A19.63  pure-longitudinal actual source support
A19.64  pattern-sensitive confinement classification
A19.65  low-degree tame or literal quadratic square
A19.66  honest lower first-nonfacet cross-facet carrier
A19.67  balance-free finite-support affine ray
A19.68  prescribed-positive singular boundary exponent
A19.69  genuine transition away from the starting facet
A19.70  exact rank-three boundary residual reduction
A19.71  exhaustive zero-clock terminal residual assembly
A19.72  contact-zero affine ray to RationalRigidity terminal or codimension two
A19.73  `.qs` strict-low ray reduction with retained carrier provenance
```

At A19.55 the singular nonlinear top face has the exhaustive balance-free split

```text
rank three on a coordinate facet
OR
codimension two.
```

The rank-three route is then pushed through honest source/cross-facet geometry rather than torus-balance assumptions.

## 6. Exact ray exposure and positive ray Rees are verified

The balance-free lower ray is not merely a face-of-a-face. A19.103/A19.104a collapse the nested finite exposures into one exact source exposure:

```text
initialForm W L F = C.ray.face
```

for the actual represented determinant-one source `F`.

Relevant owners include:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectExposure.lean`
- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayDirectInitialForm.lean`.

A19.104b/A19.110 then constructs a positive natural ray-leading reverse-Rees package with

```text
specialFiber = exact locked ray
positive Hessian defect
level < defect
2 * level < defect.
```

This is in

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees.lean`.

The all-layers-preclosing theorem is also verified:

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayAllLayersPreclosing.lean`.

These are extremely useful local laboratories, but the positive auxiliary ray defect is **not** the original zero blocker defect.

## 7. Verified `.pr` contact carrier rigidity

For the surviving `.pr` branch, the entire honest contact face satisfies

\[
d_0+d_1\le1
\]

for every supported monomial. This is the theorem

```text
pr_contact_support_pair_le_one
```

in

- `AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineCarrier.lean`.

Thus the actual contact carrier is affine in `(x0,x1)`:

\[
\Phi=x_0 A(z,w)+x_1 B(z,w)+C(z,w).
\]

The same file proves the leading high-longitudinal source slice enters at **positive contact order** (`pr_qN_pos`).

The contact Hessian calculation gives a zero `(0,1)` block and reduces the determinant to the square of the mixed determinant, so the singular contact face satisfies

\[
A_zB_w-A_wB_z=0.
\]

This is a binary Jacobian-zero / functional-dependence condition, substantially more special than a generic planar Keller pair.

## 8. Verified finite binary-profile terminal consumer

The downstream profile/staircase contradiction is essentially finished once two active-pivot/profile product coefficients are zero.

`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfilePivotExtremalCancellation.lean` proves the exact two-step cancellation theorem and the terminal consumer

```text
pr_impossible_of_two_exposed_profilePivotProduct_coeffs
```

at the two exposed orders

\[
q_{NN}=2D-r(2N),\qquad q_{NM}=2D-r(N+M).
\]

The extremal-support machinery proves there is no binary profile-Hessian support below `qNN` or strictly between `qNN` and `qNM`, so only these two product vanishings are needed. No all-depth product clock is required.

The stationary finite staircase arithmetic itself is already mature in

- `AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseTerminalArithmetic.lean`
- `AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileRigidity.lean`.

## 9. Why the old direct contact-coefficient route is genuinely blocked

`PR34_REES_EXTREMAL_OBSTRUCTION.md` records an exact symbolic obstruction to the tempting shortcut.

The model

\[
F(\varepsilon,x,y,z,w)=xh^2+yh^3+\varepsilon(2x+3hy)^2,
\qquad h=zw,
\]

satisfies the expected reverse weighted-Rees/Euler identities and has the affine locked special fibre. Yet bordered Schur correction terms survive at the relevant contact coefficient. The two-factor `prLayer_mul_leading` lemma does not control the full four-factor bordered/coupling convolution.

A second support test shows why leading-index minimality is insufficient: earlier parameter layers at **lower longitudinal indices** can feed the later four-factor convolution even though the leading longitudinal index `N` has no earlier layer.

Therefore the following inference is invalid:

```text
full Hessian clock
+ qN minimal at longitudinal index N
=> activePivot * profileDet coefficient = 0.
```

Any direct completion of this route must use stronger terminal geometry or a genuinely global pair of determinant equations. This is why the newer source-exposed/static-carrier route is attractive.

---

# Part II — Existing paper candidates that must not be confused with Lean theorems

## 10. Source-honest first-ray Schur closure

`docs/RAY_SOURCE_HONEST_SCHUR_CLOSURE.md` is a paper candidate for the rank-three `.qs` ray whose outside endpoint is rank three on `.pr`, `.sp`, or `.rq`.

In cyclic notation, let the outside facet omit coordinate `j`, with active transverse pair `(k,l)`. The exact two-term ray is

\[
G=a x_jx_k^B x_l^C+b x_0x_k^Qx_l^R,
\]

with

\[
BR=CQ,\qquad 0<Q<B,\qquad 0<R<C.
\]

The two cross-Hessian row vectors are division-free proportional. For the cleared Schur block

\[
S=\begin{pmatrix}A&H\\H&C_0\end{pmatrix}
\]

one obtains

\[
\beta H=\alpha mA,
\qquad
\beta^2C_0=\alpha^2m^2A,
\qquad
AC_0=H^2.
\]

The retained transverse Hessian minor gives `C0 != 0`, hence `A != 0`. Differentiating the proportionality gives the raw projective wedge

\[
A\partial_kH-H\partial_kA\ne0.
\]

The standard negative-square identity then gives

\[
A^2\det(\partial_kS)
=-(A\partial_kH-H\partial_kA)^2\ne0.
\]

This is exactly rank-two derivative-Schur geometry living on an **exact source initial form**. The proposed global adapter should use this geometry to license a same-family rank-one-to-rank-two repair promotion, rather than identifying the auxiliary ray clock with the original zero blocker clock.

**Status:** mathematically strong paper candidate, not yet compiled. Same-carrier codimension two is separate.

## 11. Zero-defect two-weight planar consumer

`docs/ZERO_DEFECT_TWO_WEIGHT_PLANAR_CLOSURE.md` records a different conditional consumer.

If an honest positive-family-contact terminal is built on the same blocker whose Hessian defect is zero, the first-contact exposure weight `W` and terminal two-zero cocharacter give, after standardization,

\[
W=(0,s,u,v),\qquad 2M=s+u+v.
\]

Positive contact provenance forces `s>0`. If the terminal doubling form is

\[
F=zA(x,y)+wC(x,y),
\]

then top `y`-degree support gives

\[
s\deg_yA+u\le M,
\qquad
s\deg_yC+v\le M,
\]

so

\[
\deg_yA+\deg_yC\le1.
\]

The constant planar Jacobian then makes the pair triangular-invertible, contradicting the inherited collision.

The missing hypothesis is substantive: the current A19.53/A19.52 zero-clock packet supplies a spatial/longitudinal first departure, not automatically a positive **family-parameter** contact on the same blocker.

**Status:** useful consumer, not the current unconditional closure.

---

# Part III — New paper mathematics from the current closure push

## 12. Motivation: freeze the moving correction staircase into a static source carrier

The old `.pr` contact coefficient problem is hard because several parameter and longitudinal layers can enter the same Schur correction coefficient.

The newer idea is to work directly with the source-exposed locked ray and refine the **support**, not the parameter series. The determinant-one source gives singularity of a positive-defect initial form automatically, so later repairs are frozen into one finite polynomial carrier rather than appearing as moving Rees corrections.

The locked `.pr` ray can be written

\[
v=(0,1,kU,kV),
\qquad
w=(1,0,\ell U,\ell V),
\qquad
k>\ell>0,\ U,V>0.
\]

Put

\[
s=k-\ell>0,
\qquad
h=z^Uw^V.
\]

Then the ray polynomial has the form

\[
F_{\rm ray}=a\,y h^k+b\,x h^\ell.
\]

Its lattice direction is

\[
d=w-v=(1,-1,-sU,-sV).
\]

## 13. First defect-neutral refinement: pair degree

Use the secondary exponent functional

\[
\eta_{\rm pair}(e)=-(e_0+e_1).
\]

It is constant at `-1` on the entire locked ray. Every strict-low nonlinear witness with `e0 >= 2` has strictly smaller value.

The functional is Hessian-defect neutral:

\[
4(-1)-2\bigl((-1)+(-1)+0+0\bigr)=0.
\]

Starting from a positive ray exposure `(W,L)` with

\[
\Delta=4L-2\sum_iW_i>0,
\]

the first-superface combination has the schematic form

\[
W'=AW-B\eta_{\rm pair}
=AW+B(1,1,0,0),
\]

\[
L'=AL+B,
\]

and therefore

\[
4L'-2\sum_iW'_i=A\Delta>0.
\]

Thus the first pair-nonlinear superface, once constructed as an exact source initial form, is Hessian-singular for a source-honest determinant-one reason. No invalid inheritance of singularity from the smaller ray is used.

Every exponent `e` on this first superface satisfies the resonance equation

\[
A\bigl(L-W\cdot e\bigr)
=B\bigl((e_0+e_1)-1\bigr).
\]

This turns the moving repair staircase into one finite weighted carrier.

**Status:** the defect calculation is exact paper algebra. The precise Lean/source support construction of this new superface is not yet implemented.

## 14. Second neutral direction and intended planar refinement

The space of exponent weights which are both constant on the locked ray and Hessian-defect neutral is two-dimensional.

Besides `eta_pair`, one convenient independent direction is

\[
\eta_{\rm skew}
=
\bigl(
 s(U-V),
 0,
 1-(k+\ell)V,
 (k+\ell)U-1
\bigr).
\]

A direct check gives

\[
\eta_{\rm skew}\cdot v
=
\eta_{\rm skew}\cdot w
=k(U-V)
\]

and

\[
4k(U-V)-2\sum_i(\eta_{\rm skew})_i=0.
\]

The intended use is to refine the finite first nonlinear superface once more while retaining the entire ray and at least one nonlinear point. Because this second functional is neutral, a sufficiently positive lexicographic lift should preserve positive Hessian defect.

After two independent equalities, support lies in an affine exponent plane containing the ray direction `d`.

**Important:** the linear algebra of neutrality is exact. The full finite-support lemma guaranteeing the desired second strict ray-containing refinement with positivity preserved still needs to be written/proved cleanly. Treat “planar carrier exists” as a paper construction candidate, not a compiled theorem.

## 15. Geometry of a planar carrier

Assume the intended planar refinement has been obtained. The plane contains the ray direction

\[
d=(1,-1,-sU,-sV),
\]

on which pair degree

\[
q(e)=e_0+e_1
\]

is constant.

Therefore each fixed-pair-degree slice of the plane is a lattice line parallel to `d`.

With

\[
Y=h^s y,
\]

each slice has the form

\[
M_n(z,w)\,B_n(x,Y),
\]

where `M_n` is a transverse monomial/Laurent monomial and `B_n` is binary homogeneous.

If `e` is a primitive second plane direction and

\[
g=e_0+e_1>0,
\]

then the allowed pair degrees form an arithmetic progression

\[
1,\ 1+g,\ 1+2g,\ldots,1+Ng.
\]

The four-variable correction problem has therefore become a finite two-dimensional toric profile.

---

# Part IV — The one-variable recurrence is settled on paper

## 16. Line-supported Hessian rigidity theorem

This is now recorded in

- `docs/LINE_SUPPORTED_HESSIAN_RECURRENCE_CLOSURE.md`.

Let

\[
\alpha,\beta,n,p,q>0
\]

and consider a polynomial supported on the lattice line

\[
(0,n,p,q)+\mathbb Z(1,-1,-\alpha,-\beta).
\]

Write it as

\[
H(x,y,z,w)
=y^n z^p w^q\,b(T),
\qquad
T=\frac{x}{y z^\alpha w^\beta},
\]

where `b(T)` is a polynomial, `b(0) != 0`, and the supported exponents remain nonnegative.

Assume

\[
\det\operatorname{Hess}H=0.
\]

The paper theorem is

\[
\boxed{\deg b\le1.}
\]

So every nonconstant singular line slice contains exactly two adjacent lattice monomials.

## 17. Exact ODE reduction

Set

\[
E=T\frac d{dT},
\qquad
Z=\frac{Eb}{b}=T\frac{b'}b.
\]

Let

\[
r=(0,n,p,q),
\qquad
d=(1,-1,-\alpha,-\beta),
\]

and

\[
\lambda=r+Zd
=(Z,n-Z,p-\alpha Z,q-\beta Z).
\]

After dividing by the common monomial/H factors, the Euler-scaled Hessian has the rank-one-plus-rank-one form

\[
M(Z,EZ)
=\lambda\lambda^T-\operatorname{diag}(\lambda)+(EZ)dd^T.
\]

The unperturbed determinant factors as

\[
C(Z)
=
-Z(Z-n)(\alpha Z-p)(\beta Z-q)
\bigl((\alpha+\beta)Z-(n+p+q-1)\bigr).
\]

Put

\[
\rho=\frac{n+p+q-1}{\alpha+\beta}.
\]

The Sherman--Morrison / determinant-lemma calculation gives

\[
\det M=C(Z)\bigl(1-S(Z)EZ\bigr),
\]

where

\[
S(Z)=
\frac1Z-
\frac1{Z-n}-
\frac{\alpha}{Z-p/\alpha}-
\frac{\beta}{Z-q/\beta}+
\frac{\alpha+\beta}{Z-\rho}.
\]

For nonconstant `b`, `Z(T)` is nonconstant, so `C(Z)` cannot vanish identically. Hence

\[
S(Z)EZ=1.
\]

## 18. Rational first integral and degree-one collapse

Define

\[
\Phi(Z)
=
\frac{Z(Z-\rho)^{\alpha+\beta}}
{(Z-n)(Z-p/\alpha)^\alpha(Z-q/\beta)^\beta}.
\]

Then

\[
\frac{\Phi'}\Phi=S.
\]

Therefore

\[
E(\Phi(Z(T)))=\Phi(Z(T)),
\]

so in characteristic zero

\[
\Phi(Z(T))=cT.
\]

Both `Phi` and `Z(T)` are nonconstant rational maps. Degree multiplicativity gives

\[
\deg\Phi\cdot\deg Z=1,
\]

hence

\[
\deg\Phi=1.
\]

The numerator roots of `Phi` are `0` with multiplicity `1` and `rho` with multiplicity `alpha+beta`. The denominator roots are

\[
n\ (1),\qquad p/\alpha\ (\alpha),\qquad q/\beta\ (\beta).
\]

Because the denominator roots are positive, zero never cancels. Degree one therefore forces all but one denominator degree to cancel at `rho`. There are only three possibilities:

1. `p/alpha = q/beta = rho`, forcing `n=1`;
2. `alpha=1` and `n=q/beta=rho`, forcing `p=1`;
3. `beta=1` and `n=p/alpha=rho`, forcing `q=1`.

In every case the reduced map is

\[
\Phi(Z)=\lambda\frac Z{Z-1}.
\]

Thus

\[
Z=\frac{\nu T}{1+\nu T}
\]

and

\[
(1+\nu T)b'=\nu b.
\]

Coefficient comparison gives `b_j=0` for every `j>=2`.

**Conclusion:** the finite recurrence is completely closed on paper. It does not merely terminate eventually; it cannot get past the first adjacent lattice step.

**Status:** paper candidate, not Lean-verified.

---

# Part V — Strongest current `.pr` normal form after line rigidity

## 19. Highest nonlinear slice is primitive

Apply the line theorem to the highest nonzero nonlinear pair-degree slice of the intended planar carrier.

The classification case `n=1` is impossible because this is a genuinely nonlinear slice with pair degree `n>1`.

Therefore, up to swapping the transverse coordinates, the only surviving case is

\[
\alpha=1,
\qquad p=1,
\qquad q=\beta n.
\]

For the actual `.pr` line direction

\[
\alpha=sU,
\qquad
\beta=sV,
\qquad
s=k-\ell,
\]

`alpha=1` forces

\[
\boxed{s=1,\qquad U=1.}
\]

Write

\[
V:=\beta>0.
\]

The original locked ray therefore sharpens to

\[
\boxed{
 v=(0,1,\ell+1,(\ell+1)V),
 \qquad
 w=(1,0,\ell,\ell V)
}
\]

with step

\[
\boxed{d=(1,-1,-1,-V).}
\]

The highest nonlinear slice is exactly

\[
\boxed{
 a=(0,n,1,Vn),
 \qquad
 b=(1,n-1,0,V(n-1)),
 \qquad n>1.
}
\]

It has the same step `d`.

## 20. The two rays form a lattice parallelogram

A direct calculation gives

\[
\boxed{a+w=b+v.}
\]

Thus the four extreme monomials form a single lattice parallelogram.

Writing

\[
h=zw^V,
\]

the bottom ray is

\[
A\,y h^{\ell+1}+B\,x h^\ell
=h^\ell(Bx+A yh),
\]

while the top ray is

\[
C\,y^n z w^{Vn}+D\,x y^{n-1}w^{V(n-1)}
=y^{n-1}w^{V(n-1)}(Dx+C yh).
\]

Therefore both rays are binary linear forms in the same two expressions `x` and `y h`.

## 21. First mixed determinant coefficient

A symbolic/log-Hessian calculation for the sharpened exponent geometry gives the mixed coefficient with three copies of the top right endpoint `b` and one copy of the original bottom left endpoint `v`:

\[
\boxed{
V\,\ell\,(V+1)(\ell+1)(n-1)^3
}
\]

up to the corresponding nonzero source coefficient product.

This scalar is nonzero in characteristic zero for the live integral parameters.

However, the source exponent `3b+v` may in principle be reached by other four-fold sums involving intermediate pair-degree slices. Therefore this coefficient cannot yet be declared isolated in the full planar carrier.

**Status:** useful paper calculation, not yet a branch contradiction.

## 22. Current immediate seam: full four-monomial two-ray compatibility

Ignore intermediate slices momentarily and take the extremal four-monomial carrier

\[
F=A X^v+B X^w+C X^a+D X^b
\]

with

\[
a+w=b+v.
\]

Because there is only one affine lattice relation among these four exponents, every genuinely mixed determinant cancellation should depend on one coefficient cross-ratio mismatch. The next concrete calculation is to compute/factor

\[
\det\operatorname{Hess}F
\]

for the symbolic integer parameters `ell,V,n` and classify exactly when it is zero.

The hoped-for outcome is a factor of the form

```text
(nonzero monomial/integer scalar) * (one coefficient cross-ratio mismatch)^2
```

or an equivalent rank-one relation. If singularity forces the two binary linear forms

\[
Bx+A yh,
\qquad
Dx+C yh
\]

to be proportional, then the two extremal rays lie on one common ruling. That would drastically restrict, and possibly eliminate, the entire planar carrier.

**This factorization has NOT yet been proved. It is the exact current paper seam.**

After this four-monomial calculation, one must still prove that intermediate pair-degree slices cannot evade the resulting extremal relation. The line-rigidity theorem should make this manageable: every highest remaining slice is itself only an adjacent primitive two-term ray, so one can descend finitely from the top.

---

# Part VI — Branch ledger: what is actually left locally

## 23. Rank-three other-facet ray branch

There are now two plausible paper closures:

### Route A — source-honest Schur geometry

Use `RAY_SOURCE_HONEST_SCHUR_CLOSURE.md`:

```text
exact source-exposed two-term ray
-> direction-locked cross rows
-> nonzero Schur projective wedge
-> nondegenerate derivative Schur block
-> geometry-gated rank-one -> rank-two same-family progress
```

This route is short if the global geometry adapter is accepted/formalizable.

### Route B — defect-neutral planar carrier

Use the new route:

```text
exact source-exposed ray
-> first neutral pair-degree superface
-> second independent neutral refinement
-> positive-defect singular planar carrier
-> line-supported highest slice
-> line rigidity => primitive adjacent top ray
-> finite two-ray compatibility
-> eliminate top slice / descend
```

This route is algebraically more self-contained and avoids the disputed auxiliary clock/global adapter, but currently has more paper lemmas to formalize.

The two routes are complementary; do not mix their clocks.

## 24. Same-carrier codimension-two branch

This remains a separate live mathematical obligation.

Existing paper calculations around a codimension-two homogeneous corner are encouraging. For

\[
v=(0,A,B,0),\qquad A,B>0,
\]

a one-sided departure

\[
u=(m,P,Q,R),\qquad m>0
\]

has an isolated mixed determinant coefficient proportional to

\[
ABRm(D-1)(R+m-1),
\]

forcing `R=0` in the relevant isolated setting.

For two independent departures

\[
u=(m,P,Q,0),
\qquad
w=(0,R,S,n),
\qquad m,n>0,
\]

a mixed coefficient gives

\[
-ABmn(m-1)(n-1)(D-1),
\]

so at least one departure is primitive. In the doubly primitive case another coefficient forces proportional transverse exponents; in asymmetric cases further coefficients force a unit active exponent and a three-linear-form / constant-kernel cone normal form.

There is also the top-slice factorization

\[
(B-1)\det\operatorname{Hess}_4(x_0^A G)
=-A(D-1)x_0^{4A-2}G\det\operatorname{Hess}_3G,
\]

which reduces a singular maximal `x0`-slice to a ternary Hesse problem when `B>1`.

The main source-honest difficulty is promoting such local cone/kernel behavior across lower slices or showing that the first kernel-breaking slice itself yields a contradiction.

Existing verified infrastructure useful here includes:

- `LongitudinalHessianTopDegree.lean`
- product-coordinate obstruction modules
- quadratic longitudinal boundary/source modules
- kernel-opening and stationary rank-two geometry owners.

**Status:** still open. Do not claim the new `.pr` line theorem closes this branch unless a real reduction is proved.

## 25. Cyclic `.sp` / `.rq` versions

Most rank-three other-facet geometry is cyclic. Once the `.pr` algebra is stated in coordinate-free/cyclic form, `.sp` and `.rq` should follow by the existing Schur permutations and coordinate permutations.

The primitive line theorem itself is state-free and already symmetric in the two decreasing transverse coordinates.

---

# Part VII — Relation to JC2

## 26. Global logical relation

The repository contains an exact planar Keller embedding into HC4: a planar pair `(A,C)` can be embedded via

\[
F=X_2A(X_0,X_1)+X_3C(X_0,X_1),
\]

with four-dimensional Hessian determinant equal to the square of the planar Jacobian, and a planar collision lifts to a gradient collision.

Therefore unrestricted HC4 implies planar JC2. No honest final proof can be globally weaker than JC2 in logical consequence.

## 27. Why the current local branch can still be much easier

The surviving HC4 terminal carries much more provenance than an arbitrary planar Keller pair:

- zero-clock strict-low source geometry;
- an exact rank-three exposed ray;
- direction lock;
- positive source weights with quadratic clock margin;
- affine `(x0,x1)` contact support;
- nonzero active Hessian pivots;
- finite-support extremal geometry;
- and, in the new route, defect-neutral source refinements.

So it is entirely plausible for this particular normal form to be closed without invoking a standalone JC2 theorem. That would simply mean the HC4 reduction itself has encoded the extra mathematics needed to settle JC2 as a consequence.

Do not write “we have bypassed JC2 globally.” The correct statement is: **the current local seam is no longer a generic JC2 endpoint.**

---

# Part VIII — Exact remaining programme to unrestricted HC4

The shortest honest route from the current head is the following.

## 28. M1 — settle the finite two-ray compatibility theorem on paper

Starting from

\[
v=(0,1,\ell+1,(\ell+1)V),
\]

\[
w=(1,0,\ell,\ell V),
\]

\[
a=(0,n,1,Vn),
\]

\[
b=(1,n-1,0,V(n-1)),
\]

with

\[
a+w=b+v,
\qquad
\ell,V>0,\ n>1,
\]

compute the exact Hessian determinant of

\[
F=A X^v+B X^w+C X^a+D X^b.
\]

Target theorem: classify all coefficient quadruples `(A,B,C,D)` for which the Hessian determinant vanishes.

Preferred outcome: singularity forces equality of the two endpoint coefficient ratios, equivalently a common binary ruling in `x` and `yzw^V`.

Acceptance condition: exact symbolic/algebraic factorization, not numerical evidence.

## 29. M2 — lift two-ray compatibility to the whole planar carrier

Assuming the planar refinement lemma, choose the highest nonlinear pair-degree slice. Line rigidity makes it a primitive adjacent two-term ray. Use the M1 theorem against the original locked ray.

Then either:

- the top slice is impossible outright; or
- it is forced onto the same ruling as the lower ray.

In the second case, use the next-highest slice and descend. Because pair degrees form a finite arithmetic progression and every highest slice is affine by the line theorem, the descent is finite and should not require a new well-founded global measure.

Target endpoint: no strict nonlinear planar superface can contain the locked ray.

This contradicts the first neutral refinement, which was constructed using an actual strict-low nonlinear source point.

## 30. M3 — finish the source-honest planar-refinement lemma

Before formalization, tighten the support theorem:

1. first neutral pair-degree refinement exists and is strict;
2. its exposing weight can be chosen positive with defect a positive multiple of the ray defect;
3. a second independent neutral refinement can be chosen to retain the whole ray and at least one nonlinear point;
4. after lexicographic lifting, the final coordinate weight is positive and its Hessian defect remains positive;
5. the final exact source initial form has support in an affine plane.

This is the main geometric lemma needed to make M1/M2 relevant to the actual source.

If this second-refinement lemma fails, identify the exact obstruction. A failure because the first nonlinear face is already one-dimensional or because the skew functional is constant may itself simplify the carrier enough to bypass the planar step.

## 31. M4 — close the same-carrier codimension-two branch

Use the canonical A19.55/A19.69 codimension-two provenance, not an arbitrary model.

Most promising route:

```text
canonical exposed codim-two vertex
-> exact mixed determinant coefficients
-> primitive departure or constant-kernel cone
-> if kernel persists, consume with existing kernel/rank-two geometry
-> if kernel breaks, analyze the first kernel-breaking source layer
-> use LongitudinalHessianTopDegree / quadratic-source consumers
```

Alternative: construct a defect-neutral planar/line carrier adapted to the codimension-two face if the same idea extends naturally.

Acceptance condition: unconditional contradiction or certified global progress for every codimension-two residual emitted by the current A19 assembly.

## 32. M5 — choose the shortest rank-three other-facet formal route

Once the paper mathematics is clear, decide between:

- formalizing `RAY_SOURCE_HONEST_SCHUR_CLOSURE.md`; or
- formalizing the planar/line two-ray closure.

Do not formalize both unless one supplies reusable lemmas for the other.

The source-honest Schur route probably needs fewer new polynomial calculations. The planar route may be logically cleaner because singularity is obtained directly from positive-defect source initial forms and avoids the auxiliary-clock/global-progress interpretation.

## 33. M6 — Lean formalization order

For the planar route, a minimal dependency order is:

1. **state-free line Hessian algebra**
   - Euler-scaled Hessian formula for `X^r b(X^d)`;
   - determinant rank-one update;
   - factorization of `C(Z)`;
   - logarithmic derivative identity for `Phi`.

2. **rational-function rigidity**
   - `E R = R -> R = c*X`;
   - rational-map degree multiplicativity in the required specialized form;
   - finite cancellation arithmetic for the roots/multiplicities.

3. **line-profile conclusion**
   - `(1+nu*X) * derivative b = nu*b`;
   - `natDegree b <= 1`.

4. **source support adapters**
   - first neutral superface;
   - second neutral planar refinement;
   - fixed pair-degree line extraction;
   - highest-slice parameters.

5. **four-monomial two-ray theorem**
   - state-free first;
   - source adapter second.

6. **cyclic wrappers** for `.pr/.sp/.rq`.

7. **terminal consumer** returning `False` or certified global rank-two progress.

For the Schur route, reuse as much as possible from existing B38/projective-wedge and presented-blocker geometry owners rather than rebuilding rank-two packets.

## 34. M7 — splice terminal impossibility into existing assembly

Once all A19.73 residual cases are consumed, prove the unconditional presented-terminal impossibility expected by the existing reachable-terminal reduction.

Then reuse:

```text
gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
```

and the existing HC4 reduction front door.

No new global recursion should be necessary.

## 35. M8 — final theorem and proof audit

The final acceptance criterion is not “paper argument looks complete.” It is:

- top-level unrestricted HC4 theorem elaborates;
- full repository build is green;
- axiom audit is clean under the project’s accepted assumptions;
- negative/escape-hatch tests remain green;
- no hidden JC2 theorem is imported unless intentionally part of the proof;
- `CURRENT_STATE.md`, `PROOF_PATHS.md`, and generated module/declaration indices are updated to match the actual theorem graph.

---

# Part IX — Things not to do

## 36. Do not identify the auxiliary ray clock with the zero blocker clock

This mismatch is already formally proved. The zero terminal has defect zero; the ray package has positive defect. The ray clock is a useful local device, not the original stationary clock.

## 37. Do not assume full family-parameter first contact from A19.52

A19.52 gives a spatial/longitudinal departure in the special fibre. It is not automatically a positive family-parameter layer. This is why the two-weight planar consumer remains conditional.

## 38. Do not drop bordered/coupling Schur corrections

`PR34_REES_EXTREMAL_OBSTRUCTION.md` gives explicit examples where they survive. The contact raw complement and the parameter residual are different objects.

## 39. Do not use leading-index minimality as whole-family sparsity

`contactLongitudinalParameterLayer q N = 0` for `q<qN` does not mean `familyParameterLayer q = 0`. Lower longitudinal indices may occur earlier and contaminate four-factor products.

## 40. Do not silently promote paper candidates to Lean facts

In particular the following are **not yet Lean theorems** at this handoff:

- source-honest ray Schur global closure;
- zero-defect two-weight terminal consumer in its generic same-blocker form;
- defect-neutral first nonlinear source-superface construction;
- defect-neutral second planar refinement;
- line-supported Hessian rigidity theorem;
- primitive highest nonlinear ray adapter;
- four-monomial two-ray compatibility theorem;
- elimination of the full planar nonlinear superface;
- unconditional codimension-two terminal contradiction;
- unrestricted HC4.

---

# Part X — Immediate next-session instructions

## 41. First action: finish the four-monomial determinant

Do **not** reopen the old qNN/qNM contact convolution problem first.

Start with the exact current paper normal form

\[
F=
A\,y(zw^V)^{\ell+1}
+B\,x(zw^V)^\ell
+C\,y^n z w^{Vn}
+D\,x y^{n-1}w^{V(n-1)}.
\]

Equivalently, with `h=z w^V`,

\[
F=h^\ell(Bx+A yh)
+y^{n-1}w^{V(n-1)}(Dx+C yh).
\]

Compute and factor `det Hess F` symbolically over

```text
A,B,C,D, ell,V,n
```

under positive-integral `ell,V` and `n>=2`.

Use log-scaled monomial Hessians if they make the factorization cleaner. Track all coefficient factors exactly.

Questions to answer:

1. Does `det Hess F = 0` force `AD = BC`, `AC = BD`, or another single cross-ratio relation depending on coefficient ordering?
2. If a common binary linear factor is forced, what is the exact factorization of `F`?
3. Does the factored form fall directly under an existing product-coordinate / constant-kernel / RationalRigidity obstruction?
4. If the four-term carrier itself is singular for a genuine family of coefficient ratios, what additional determinant coefficient from the next-lower planar slice kills it?

Only after this exact four-term theorem is known should the full finite descent be designed.

## 42. Second action: audit the neutral planar support lemma

Write the finite-support statement precisely and prove it on paper before Lean:

```text
positive source exposure of locked ray
+ actual source point with pair degree > 1
+ two independent defect-neutral functionals constant on ray
=> positive-defect exact source initial form
   containing the entire ray and a nonlinear point
   whose support is contained in an affine plane.
```

If the conclusion needs a slightly weaker statement (for example a union of parallel line slices rather than literal affine-plane equality), use the weakest sufficient form.

## 43. Third action: only then formalize

Once the two-ray theorem and support lemma are stable, formalize the state-free line theorem and two-ray algebra first. Keep source-state plumbing out of those files.

---

# Part XI — Bottom line

The unrestricted HC4 project is genuinely at a late local-closure stage, but it is not yet proved.

What is complete:

- unrestricted collision entry;
- canonical degree choice;
- global rank-one recursion;
- successful Rees restart edges;
- positive reached-rank-three consumption;
- producer-free zero-clock strict-low terminal;
- singular top-face/boundary geometry;
- honest first-nonfacet/cross-facet ray extraction;
- exact source exposure of the locked ray;
- extensive `.pr` Schur/profile infrastructure;
- finite profile terminal consumer;
- several source-level model/kernel/quadratic obstruction modules.

What is newly settled on paper:

- the one-variable finite line recurrence: a nonconstant singular line profile is necessarily affine;
- therefore a highest nonlinear line slice is exactly a primitive two-monomial ray;
- in the live `.pr` specialization this forces `k-ell=1`, `U=1` (up to the transverse swap) and the explicit parallel/parallelogram normal form above.

What remains mathematically:

1. finish the finite two-ray compatibility theorem and use it to eliminate the full nonlinear planar superface;
2. prove the defect-neutral planar source-refinement lemma rigorously;
3. close the separate same-carrier codimension-two terminal branch.

What remains formally after that:

4. encode the chosen paper closures in Lean;
5. consume every A19 terminal residual;
6. splice terminal impossibility into the already-existing trace collapse / unrestricted HC4 front door;
7. run the full proof/axiom/escape-hatch audit.

The next genuinely high-value calculation is therefore the **four-monomial parallelogram Hessian determinant**. It is finite, explicit, and directly adjacent to the current source geometry. If it produces the expected common-ruling factorization, the rank-three `.pr` branch will be very close to a complete paper closure.
