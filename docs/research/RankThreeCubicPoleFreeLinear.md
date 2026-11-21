# Cubic characteristic: pole-free rational velocity is linear

## Mathematical statement

Work over a characteristic-zero field \(K\) and put
\(B=K[y_1,y_2,y_3]\). Suppose a transverse polynomial Hessian
block \(H(y)\in M_3(B)\) has \(\det H\ne0\), every entry of
\(H\) is homogeneous of degree one, and
\(r(y)\in B^3\) is homogeneous of degree two.

Let \(V\in \operatorname{Frac}(B)^3\) solve
\[
 H(y)V(y)=r(y).
\]
If **each coordinate of \(V\) lies in \(B\)** (the pole-free branch),
then there is a constant \(N\in M_3(K)\) such that
\[
 \boxed{V(y)=Ny}.
\]

No explicit adjugate numerator or Jordan normal form is needed.
The degree-one conclusion follows from the Hessian equation.

## Proof by the Euler operator

Define \(E=\sum_{j=1}^3 y_j\partial_{y_j}\).
For a homogeneous polynomial \(f\) of degree \(d\), Euler's
identity gives \(Ef=df\). Writing \(V=W\in B^3\),
the product rule yields
\[
 E(HW)=(EH)W+H(EW)=HW+H(EW).
\]
The right side of \(HW=r\) has degree two, so
\[
 HW+H(EW)=2r=2HW,\quad H(EW-W)=0.
\]
Multiplying by \(\operatorname{adj}(H)\) gives
\(\det H\,(EW-W)=0\). Since \(B\) is a domain and
\(\det H\ne0\), \(EW=W\).

For completeness, the converse to Euler's identity in
characteristic zero follows coefficient by coefficient:
\[
 [y^m]Ef=|m|[y^m]f.
\]
Thus any monomial occurring in \(W_i\) has total degree one.
Equivalently, each \(W_i\) is a constant-coefficient
linear form \(\sum_j N_{ij}y_j\).

An independent check uses Cramer's formula: the determinant of
a three-by-three matrix of linear forms has degree three,
while the adjugate applied to a quadratic vector has degree
four. A polynomial quotient must therefore have degree one.

## Scope and Lean obligations

The proposed module is
`HC4/Polynomial/RankThreeCubicPoleFreeLinear.lean`.
It provides:
- a coefficient converse to Euler's identity;
- homogeneous \(3\)/\(4\) quotient rigidity;
- extraction of a constant linear form via derivatives at zero;
- homogeneous Hessian equation rigidity;
- a fraction-field version with the **explicit pole-free
  representative** hypothesis.

**The pole-free premise is not proved for every rational characteristic.**
Showing that either the characteristic has polynomial coordinates or
there is a useful denominator prime is the next algebraic branch.
Furthermore, applying this to the exact source requires proving the
homogeneous Hessian and mixed-derivative input equations from the
source's cubic transverse grade, together with the anchored
gradient-transport/Hessian-kernel equation.

These are genuine assembly obligations; neither a bare polynomial
representative nor the equation \(HW=r\) may be silently supplied at
the top-level HC4 theorem.

## Validation

The isolated [targeted Lean build](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44897863408)
and [six-theorem axiom audit](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44897905038)
passed. Each theorem depends only on the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. A full
`lake build HC4` and repository-wide audit were additionally scheduled
on the isolated validation branch; consult the workflow run rather
than inferring their result from the targeted build.

## Anchored source-characteristic Hessian kernel (Lean-verified)

In `RankThreeCubicAnchoredKernel.lean`, the first coefficient of a line
substitution is proved to be the directional derivative at the starting
point. Hence the gradient-transport identity on the **actual** cubic
produces the Hessian-kernel equation `Hessian L(z) * V = 0` at the
anchored generic point. This theorem neither assumes a polynomial
characteristic nor silently inserts the kernel equation.

The [targeted Lean build and axiom audit](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44900126494)
passed (only `propext`, `Classical.choice`, `Quot.sound`).
The remaining source-to-pole-free assembly must translate the anchored
fraction-field evaluation into the homogeneous transverse matrix and
mixed-derivative data, and separately handle denominator primes.

## Source-derived fraction-field Hessian system (Lean-verified)

The `RankThreeCubicSourceFractionKernel.lean` module now makes the
previously abstract Hessian equation **source honest**.

For any cap-three constant-Hessian-determinant source whose cubic initial
form has generically full transverse Hessian rank, the source itself
constructs a longitudinal slice `a` and normalized rational
characteristic `V`. Its transverse polynomial Hessian block `H_a`
satisfies `det H_a ≠ 0`, and, writing
`W_j = V (.inr j)` and `r_a` for minus the mixed
longitudinal/transverse derivative of the **actual** cubic initial form,
the theorem proves in the transverse polynomial fraction field
`(H_a.map algebraMap) *ᵥ W = algebraMap ∘ r_a`.

The independent matrix-kernel assumption is therefore eliminated;
the proof derives it by taking the first time coefficient of the
already constructed gradient characteristic. The generic slice is
explicitly chosen so that the polynomial Hessian determinant remains
nonzero, rather than losing this property through an existential
witness.

The [Lean 4.24 targeted build and four-theorem axiom audit](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44901484156)
succeeded, with only `propext`, `Classical.choice`, and
`Quot.sound`. This is **not** a claim that the entire `HC4`
import graph was rebuilt on that commit.

The next precise obligations are to prove that the source block
`H_a` has degree-one homogeneous entries and `r_a` has degree-two
homogeneous entries using the cubic initial-form weight, and then to
apply `exists_linear_matrix_of_poleFree_fractionKernel` to the
pole-free case. Genuine denominator primes remain open.

## Source-weight-to-transverse-degree bridge (Lean-verified)

The `RankThreeCubicSourceDegrees.lean` module converts the cubic
source's integer transverse weight into a natural weighted Euler
identity. After restricting the longitudinal variable to any
ground-field value, that identity becomes ordinary transverse Euler
homogeneity. The theorem
`referenceSlice_isHomogeneous_of_transverseWeight` proves this for
**arbitrary natural degrees**, and its two source corollaries show that
`sourceTransverseHessian a (initialForm ... 3 F)` has degree-one
homogeneous entries and
`sourceNegativeMixedHessian a (initialForm ... 3 F)` has degree-two
homogeneous entries. The earlier Euler converse was generalized and
Lean-checked as `isHomogeneous_of_transverseEuler_eq_nsmul`.

The [targeted Lean 4.24 build and four-theorem axiom audit](https://github.com/JamieLittle16/HC4_Lean_Canonical_Phase75_4/actions/runs/44902392674)
passed with only `propext`, `Classical.choice`, and `Quot.sound`.

The source now supplies the polynomial matrix equation, the
nonvanishing determinant and both degree conditions required by
`exists_linear_matrix_of_poleFree_fractionKernel`. What remains
is an explicit **source-level linear-or-pole dichotomy** applying
these statements together, and then the analysis of actual
non-polynomial rational characteristic coordinates.
