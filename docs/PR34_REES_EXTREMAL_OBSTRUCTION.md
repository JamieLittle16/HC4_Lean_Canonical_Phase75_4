# Exact Rees test of the remaining PR coefficient route

Checked against PR #34 at ef0e54a (Lean CI #1556 successful).
This note records exact symbolic research, not a new Lean theorem or an HC4
counterexample. The conditional single-coefficient consumer remains checked;
the required product-zero hypothesis has not been proved.

## A stronger local test

Over the rationals put h=zw, s=2x+3hy and

    F(e,x,y,z,w) = x h² + y h³ + e s².

This is an actual reverse weighted Rees family with D=7, weights (3,1,1,1):

    F(e,x,y,z,w) = e⁷ F(1,x/e³,y/e,z/e,w/e).

Consequently its source/parameter Euler identities hold exactly. Its leading
longitudinal data are N=2, qN=1, t=0. Its special fibre has only exponents
(1,0,2,2) and (0,1,3,3), so it has affine rational-line support and positive
locked (z,w) exponents. This checks this concrete support property, not all
of the repository's canonical endpoint or terminal hypotheses.

The special fibre's (x,y) Hessian block is zero, its mixed determinant is zero,
and its active (z,w) principal Hessian determinant is nonzero. Both binary
coefficients a=h² and b=h³ are powers of a common monomial. Thus the proposed
common-monomial conclusion is already satisfied in this test.

## The explicit surviving term is bordered

Use precisely the Euler-scaled active directions z∂z,w∂w and complementary
directions x∂x, 3x∂x+y∂y+z∂z+w∂w. Write A for the active determinant, R for
the parameter residual, and B for the three bordered terms plus the mixed
coupling square, with the conventions of ContactWeightedSchurShear.

The mixed coupling determinant is identically zero for the *whole* test
family, before taking any coefficient. Nevertheless, at the contact coefficient
[e² x⁴] the exact values are:

| Expression | Coefficient |
| --- | --- |
| R | 64 |
| Three bordered terms | -81792 y² z⁶ w⁶ |
| Mixed coupling square | 0 |
| A R | -50688 y² z⁶ w⁶ |
| B - A R | -31104 y² z⁶ w⁶ |

These are contact coefficients. They must not be called the final binary
qNN product coefficient: transverse inflation and the active pivot contribute
additional degree shifts. In particular this calculation is a diagnostic of
the suggested contact-layer cancellation, not a counterexample to a theorem
under the full terminal assumptions.

The quadratic `prLayer_mul_leading` lemma requires both factors' layers to be
scalar multiples of source layers. It does not directly apply to the active
and bordered four-factor products. Extra convolution terms cannot be discarded
by applying its two-factor conclusion to the entire correction.

## The full determinant clock supplies additional information

The determinant is exactly

    det Hess F = 576 e³ h (6ey+h) s³.

So the first two equations vanish, but the third does not. The required
repository clock would be 4D-2(contactGap+4)=16. This family fails that
hypothesis and does not have Hessian determinant one.

There is a sharper fact: arbitrary later polynomial Rees layers cannot repair
this particular prescribed F0,F1 while keeping the preceding equation zero.
Write a prospective continuation as

    F + e² G2 + e³ G3 + ...,

where Gq has weighted degree 7-q. Necessarily

    G2 = x A2(y,z,w) + B5(y,z,w),

with A2 homogeneous quadratic and B5 homogeneous of degree five. Let a be the
coefficient of y² in A2. The two determinant coefficients are

    [e² x²] det Hess = 32 a h⁴,
    [e³ x³] det Hess = 192 (24-a) h².

Thus the first equation forces a=0 and the next forces a=24, impossible in
characteristic zero.

Why omitted layers cannot affect these coefficients: every determinant term
uses exactly two x derivatives, reducing the sum of the four chosen source
x degrees by two. F0 has x degree one, F1 has x degree two, G2 has x degree
at most one, and G3 has x degree at most one. At parameter order two the
B5 contribution therefore has x degree at most one. At order three its
cross terms have x degree at most two, as does the linear G3 contribution.
Layers of order four and above do not occur. The F1-only determinant is already
zero at order two. The script checks the remaining arbitrary quadratic A2
calculation exactly.

## Consequence for the proof search

Rees/Euler structure, affine special-fibre vanishing, common-monomial planar
coefficients and even whole-family mixed-determinant vanishing do not by
themselves imply the desired contact correction vanishing. The determinant
clock must enter substantively. In this explicit case, two consecutive clock
equations give an obstruction that neither equation alone gives.

The unresolved general step is to derive such an incompatible pair, or another
valid consequence of the full clock, for arbitrary permitted leading slices
and contact carriers. No proof of that general step, PR terminal impossibility,
or unrestricted HC4 is claimed here.

Reproduce with SymPy:

    python tools/research/pr_rees_extremal_probe.py

## Why leading-index minimality does not imply a sparse family jet

The precise R18.32 conclusion is
`contactLongitudinalParameterLayer q N = 0` for `q < qN`. It does not state
`familyParameterLayer contactFamily q = 0`. Earlier layers at longitudinal
indices below N remain possible. Thus the literal first/second variation
identities cannot simply be reindexed to qN/2qN.

An exact support test uses D=9, weights (3,1,1,1), h=zw and

    F9 = x h³ + y h⁴ + λ e² x h² + e³ (3x+4hy)².

It satisfies the weighted Rees/Euler identity and has N=2, qN=3, t=0.
Its longitudinal-N coefficients at parameter orders 0,1,2 vanish, while its
order-two longitudinal-one coefficient is λh². For its Euler-scaled active
pivot A and contact profile core P, the exact coefficient is

    [e⁶ x⁴ λ³](A P) = 2592 h⁹.

This illustrates an actual four-factor convolution contribution from lower
longitudinal layers that the two-factor leading-pair lemma does not exclude.
As above, this is a contact coefficient, not the final binary product
coefficient after all degree shifts. F9 is only a support test: no full
Hessian clock or complete terminal hypotheses are asserted (in particular it
does not supply the required strict-low monomial of degree at least three
and longitudinal exponent at least two). The script checks these displayed
identities exactly.

A closing proof must use further actual terminal constraints or the full clock
to control these lower-index terms. No such general elimination is proved by
this test or by the literal order-one/order-two variation theorems.
