# Cubic squarefree-pole obstruction via Jacobi (22 November 2026)

**Status:** independent mathematical proof / Lean integration plan. **NOT an end-to-end Lean-verified theorem at this commit.** This note uses only the project's existing source-derived cubic characteristic, nonzero Cramer residue, rank-one adjugate contraction and Jacobi lemmas. No external proposed HC4 proof is invoked.

## Target

Let `K` be a characteristic-zero field and let `F ∈ K[x,y₁,y₂,y₃]` have transverse degree at most three and nonzero constant full Hessian determinant. Write `L` for its actual cubic transverse initial form. Assume the transverse Hessian of `L` is generically invertible. For a longitudinal anchor `a`, put

- `C(y) = L(a,y)`;
- `H(y) = Hess_y C(y)`, a symmetric matrix of *linear* polynomials;
- `D(y) = det H(y) ≠ 0`, a homogeneous cubic;
- `r(y) = −∂_x ∇_y L(a,y)`;
- `V(y) = H(y)^{-1}r(y)` over `Frac K[y]`.

The source characteristic gives the exact gradient transport identity along `(a+t,y+tV(y))`.

**Claim.** If `D` is squarefree, every coordinate of `V` is polynomial. By the already proved source degree-one homogeneity / pole-free linearity theorem, `V(y)=Ny` for some constant `3×3` matrix `N`. In particular, **a genuine non-polynomial cubic source characteristic forces `D` to have a repeated factor**. By the existing degree-three theorem, this factor has total degree one.

The point is to derive a contradiction at a *genuine source pole*, not to assert that an arbitrary ternary cubic has no singular direction.

## Proof of squarefree-pole impossibility

Assume for contradiction that `D` is squarefree and at least one `V_i` is non-polynomial.

### 1. Extract the actual residue

The existing reduced-denominator/Cramer machinery yields an irreducible `p ∣ D` and a nonzero vector

`S = (adj(H) r) mod p ≠ 0`

over the integral domain `R = K[y]/(p)`. It also yields a *principal* surviving cofactor `k`:

`B = adj(H) mod p`, with `B_kk ≠ 0`.

Here `B` is symmetric and `det(H) mod p = 0`. Hence every `2×2` minor of `B` is zero, so

`B_kk B_ij = B_ik B_kj`

in `R` for all `i,j`. Moreover `S = B(r mod p)`.

All of these data arise from the **same** `F,a,V,p`.

### 2. Source transport gives singular cubic equations

The coefficientwise source-residue theorem shows for each transverse coordinate `i` and every characteristic-time coefficient `n`:

`Σ_{j,k} (Q_i,jk[n] mod p) S_j S_k = 0`.

The polynomial families `Q_i,jk(t)` are exactly the transported source third derivatives. At `t=0`, the constant-term identity for `lineEval` and injectivity of `K[y] → Frac K[y]` give

`Q_i,jk[0] = ∂_{y_i} H_jk`.

Therefore

**(∗)** `Σ_{j,k} (∂_{y_i} H_jk mod p) S_j S_k = 0` for every `i`.

This constant-term equality needs a short explicit Lean transport lemma; do not replace it by an assumed identification.

### 3. Cancel the rank-one adjugate without dividing in the quotient

The existing lemma `rankOneCramer_quadratic_zero_implies_adjugate_contraction_zero` applies in `R` to `B`, `r mod p`, the nonzero principal pivot and (∗). It gives

`Σ_{j,k} (∂_{y_i} H_jk mod p) B_jk = 0`.

The cancellation is valid because `R` is a domain and `S ≠ 0`. No inverse of `p`, `B_kk` or a coordinate of `S` is assumed in `R`.

### 4. Jacobi makes the pole component singular

The source has an existing 3×3 Jacobi identity valid **even at singular matrices**:

`∂_{y_i}(det H) = Σ_{j,k} adj(H)_{kj} ∂_{y_i}H_{jk}`.

Since `H` and its adjugate are symmetric, the contraction in step 3 is exactly the reduction of this identity modulo `p`. Thus

**(†)** `p ∣ ∂_{y_i}D` for every `i`.

### 5. Contradiction with squarefreeness in characteristic zero

Write `D=ph`. Since `D` is squarefree and `p` is irreducible, `p∤h`. Differentiating and using (†):

`0 ≡ ∂_iD = (∂_i p)h + p∂_i h ≡ (∂_i p)h (mod p)`.

Primality of `p` gives `p ∣ ∂_i p` for every `i`. But a nonconstant polynomial over a characteristic-zero field has some nonzero partial derivative; any such partial derivative has strictly smaller total degree than `p`, so `p` cannot divide it. Contradiction.

Consequently `V` is polynomial whenever `D` is squarefree, and the project's pole-free linearity result makes it constant-linear in the transverse coordinates.

## Exact Lean integration frontier

The project already has:

1. `exists_sourceCubic_squarefreePole_coefficientwiseSingularResidue` in `RankThreeCubicSourceSingularCoefficientResidue.lean` (the same nonzero Cramer residue, principal cofactor, and coefficientwise quadratic transport);
2. `adjugate_rankOne_cross_products` in `RankThreeCubicAdjugateRankOneMinors.lean`;
3. `rankOneCramer_quadratic_zero_implies_adjugate_contraction_zero` in `RankThreeCubicRankOneQuadraticContraction.lean`;
4. `pderiv_det_fin_three` in `RankThreeCubicJacobiDetPderiv.lean`;
5. `exists_sourceCubic_repeated_linear_factor` in `RankThreeCubicRepeatedFactor.lean`;
6. `exists_linear_matrix_of_poleFree_fractionKernel` in `RankThreeCubicPoleFreeLinear.lean`.

**Remaining Lean bridges (all must be proved, not introduced as terminal assumptions):**

- Show that the time-zero coefficient of the source-derived `Q_i,jk` equals `pderiv i (H j k)` before reduction modulo `p`. Use `lineEval`'s constant-coefficient identity, scalar-extension injectivity, transverse partial commutation, and `referenceSlice_pderiv`.
- Transport `adjugate_rankOne_cross_products` through the quotient map; establish the image of `adj(H)` agrees with `adj(H mod p)`, prove symmetry, and instantiate rank-one Cramer cancellation with `S`.
- Use singular-safe Jacobi and the quotient kernel equivalence to prove `p ∣ pderiv i D` for every `i`.
- Prove or locate the multivariate characteristic-zero squarefree derivative criterion: `Squarefree D`, `Irreducible p`, `p ∣ D` imply some `i` with `¬ p ∣ pderiv i D`.

The desired resulting theorem should rule out **the squarefree + nonpolynomial branch of the actual cubic source characteristic**. Do not claim the repeated-linear-factor branch, the final cubic injectivity theorem or conditional HC4 is closed.

## Why this is the right next seam

This route avoids the harder geometric detour through singular points of a plane cubic. It uses the source coefficient transport already certified by the project and the exact Jacobi/adjugate lemmas developed immediately before this note. It makes the rank-one contraction theorem mathematically decisive rather than merely preparatory.

**Verification discipline:** a mathematical argument has been written here; the full theorem above is NOT yet a compiled Lean declaration. No `sorry`, auxiliary endpoint hypothesis, or inferred green CI status should be used to promote it prematurely.
