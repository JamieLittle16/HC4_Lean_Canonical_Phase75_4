import HC4.Newton.ExactCollisionFirstWall
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-!
# Transverse Smith first-wall blockers at an axis collision

Let `F` be homogeneous of degree `D` and let the collision point be the
coordinate-axis point `e_x`.

For a transverse coordinate `i != x`, consider the `i`-th gradient
component.  A support monomial can contribute nontrivially at `e_x` only
if, after differentiating once in `i`, every remaining exponent is carried
by `x`.  Homogeneity then forces the original monomial to be exactly

    x^(D-1) * X_i.

Thus `x^(D-1) X_i`, whenever it occurs in the support, is automatically the
unique nonzero contributor to the `i`-th gradient component at `e_x`.

Combining this with Phase 93.11's exact-collision theorem excludes that
monomial altogether.

Taking `i=y`, `i=z`, or `i=w` gives the three transverse low-blocker
exclusions needed by the Smith first-wall analysis, including the
`w`-linear zero-grade wall.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The transverse homogeneous blocker `x^(D-1) X_i`. -/
noncomputable def transverseAxisBlockerExponent
    (x i : σ)
    (D : ℕ) : σ →₀ ℕ := by
  classical
  exact
    Finsupp.single x (D - 1) +
      Finsupp.single i 1

/-- A nonzero contribution at `e_x` leaves, after differentiation in `i`,
an exponent supported only at `x`. -/
theorem derivativeRemainder_eq_single_axis_of_contribution_ne_zero
    [CharZero K]
    (x i : σ)
    (F : MvPolynomial σ K)
    (d : σ →₀ ℕ)
    (hcontrib :
      gradientMonomialContributionAt
        (coordinateAxisPoint (K := K) x)
        F i d ≠ 0) :
    d - (Finsupp.single i 1 : σ →₀ ℕ) =
      Finsupp.single x
        ((d - (Finsupp.single i 1 : σ →₀ ℕ)) x) := by
  classical
  let r : σ →₀ ℕ := d - (Finsupp.single i 1 : σ →₀ ℕ)
  have hprodne :
      r.prod
          (fun j e =>
            coordinateAxisPoint (K := K) x j ^ e) ≠ 0 := by
    intro hprod
    apply hcontrib
    rw [gradientMonomialContributionAt_eq]
    change
      (MvPolynomial.coeff d F * ((d i : ℕ) : K)) *
          r.prod
            (fun j e =>
              coordinateAxisPoint (K := K) x j ^ e) = 0
    rw [hprod]
    simp
  have hr_off :
      ∀ j, j ≠ x -> r j = 0 := by
    intro j hjx
    by_contra hrj
    have hjmem : j ∈ r.support :=
      Finsupp.mem_support_iff.mpr hrj
    have haxis :
        coordinateAxisPoint (K := K) x j = 0 := by
      simp [coordinateAxisPoint, hjx]
    have hfactor :
        coordinateAxisPoint (K := K) x j ^ r j = 0 := by
      rw [haxis]
      exact zero_pow hrj
    have hzero :
        r.prod
          (fun q e =>
            coordinateAxisPoint (K := K) x q ^ e) = 0 := by
      unfold Finsupp.prod
      exact Finset.prod_eq_zero hjmem hfactor
    exact hprodne hzero
  change
    r = Finsupp.single x (r x)
  apply Finsupp.ext
  intro j
  by_cases hjx : j = x
  · subst j
    simp
  · have hrj : r j = 0 :=
      hr_off j hjx
    simp [hjx, hrj]

/-- A nonzero gradient contribution implies that the differentiated
coordinate occurs with positive exponent. -/
theorem exponent_ne_zero_of_gradientContribution_ne_zero
    [CharZero K]
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ)
    (hcontrib :
      gradientMonomialContributionAt point F i d ≠ 0) :
    d i ≠ 0 := by
  intro hdi
  apply hcontrib
  rw [gradientMonomialContributionAt_eq]
  simp [hdi]

/-- **Axis contribution classification.**
For `i != x`, a homogeneous degree-`D` support monomial contributing
nontrivially to the `i`-th gradient component at `e_x` must be exactly
`x^(D-1) X_i`. -/
theorem homogeneous_transverse_contributor_eq_blocker
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (x i : σ)
    (hix : i ≠ x)
    (d : σ →₀ ℕ)
    (hd : d ∈ F.support)
    (hcontrib :
      gradientMonomialContributionAt
        (coordinateAxisPoint (K := K) x)
        F i d ≠ 0) :
    d = transverseAxisBlockerExponent x i D := by
  classical
  have hrem :
      d - (Finsupp.single i 1 : σ →₀ ℕ) =
        Finsupp.single x
          ((d - (Finsupp.single i 1 : σ →₀ ℕ)) x) :=
    derivativeRemainder_eq_single_axis_of_contribution_ne_zero
      x i F d hcontrib
  have hdi :
      d i ≠ 0 :=
    exponent_ne_zero_of_gradientContribution_ne_zero
      (coordinateAxisPoint (K := K) x)
      F i d hcontrib
  have hrem_i :
      (d - (Finsupp.single i 1 : σ →₀ ℕ)) i = 0 := by
    have hi_ne_x : i ≠ x := hix
    rw [hrem]
    simp [hi_ne_x]
  have hdi_sub :
      d i - 1 = 0 := by
    simpa using hrem_i
  have hdi_one :
      d i = 1 := by
    omega
  have hshape :
      d =
        Finsupp.single x (d x) +
          Finsupp.single i 1 := by
    apply Finsupp.ext
    intro j
    by_cases hjx : j = x
    · subst j
      simp [hix]
    · by_cases hji : j = i
      · subst j
        simp [hix, hdi_one]
      · have hrem_j :
            (d - (Finsupp.single i 1 : σ →₀ ℕ)) j = 0 := by
          have hj := congrArg
            (fun r : σ →₀ ℕ => r j) hrem
          simpa [hjx] using hj
        have hdj : d j = 0 := by
          simpa [hji] using hrem_j
        simp [hjx, hji, hdj]
  have hcoeffd :
      MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeffd
  rw [hshape] at hdeg
  have hdx :
      d x + 1 = D := by
    simpa [Finsupp.weight_single] using hdeg
  have hdx_sub :
      d x = D - 1 := by
    omega
  unfold transverseAxisBlockerExponent
  simpa [hdx_sub] using hshape

/-- The transverse blocker has exponent one in its transverse
coordinate. -/
theorem transverseAxisBlockerExponent_apply_transverse
    (x i : σ)
    (hix : i ≠ x)
    (D : ℕ) :
    transverseAxisBlockerExponent x i D i = 1 := by
  classical
  simp [transverseAxisBlockerExponent, hix]

/-- Differentiating the transverse blocker once in `i` leaves exactly the
pure axis exponent `x^(D-1)`. -/
theorem transverseAxisBlockerExponent_sub_transverse
    (x i : σ)
    (hix : i ≠ x)
    (D : ℕ) :
    transverseAxisBlockerExponent x i D -
        (Finsupp.single i 1 : σ →₀ ℕ) =
      Finsupp.single x (D - 1) := by
  classical
  apply Finsupp.ext
  intro j
  by_cases hjx : j = x
  · subst j
    simp [transverseAxisBlockerExponent]
  · by_cases hji : j = i
    · subst j
      simp [transverseAxisBlockerExponent, hix]
    · simp [transverseAxisBlockerExponent, hjx]

/-- The blocker itself contributes nontrivially whenever it belongs to the
support. -/
theorem transverseAxisBlocker_contribution_ne_zero
    [CharZero K]
    {F : MvPolynomial σ K}
    (x i : σ)
    (hix : i ≠ x)
    (D : ℕ)
    (hsupport :
      transverseAxisBlockerExponent x i D ∈ F.support) :
    gradientMonomialContributionAt
        (coordinateAxisPoint (K := K) x)
        F i
        (transverseAxisBlockerExponent x i D) ≠ 0 := by
  classical
  have hcoeff :
      MvPolynomial.coeff
        (transverseAxisBlockerExponent x i D) F ≠ 0 := by
    exact MvPolynomial.mem_support_iff.mp hsupport
  rw [gradientMonomialContributionAt_eq]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero hcoeff ?_
    rw [transverseAxisBlockerExponent_apply_transverse
      x i hix D]
    norm_num
  · rw [transverseAxisBlockerExponent_sub_transverse
      x i hix D]
    have hprod :
        (Finsupp.single x (D - 1) : σ →₀ ℕ).prod
            (fun j e =>
              coordinateAxisPoint (K := K) x j ^ e) = 1 := by
      rw [Finsupp.prod_single_index]
      · simp [coordinateAxisPoint]
      · simp [coordinateAxisPoint]
    rw [hprod]
    exact one_ne_zero

/-- A supported transverse blocker is the unique nonzero contributor to its
gradient component at the axis point. -/
theorem transverseAxisBlocker_isUniqueGradientContributor
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 1 ≤ D)
    (x i : σ)
    (hix : i ≠ x)
    (hsupport :
      transverseAxisBlockerExponent x i D ∈ F.support) :
    IsUniqueGradientContributorAt
      (coordinateAxisPoint (K := K) x)
      F i
      (transverseAxisBlockerExponent x i D) := by
  refine
    ⟨hsupport,
      transverseAxisBlocker_contribution_ne_zero
        x i hix D hsupport,
      ?_⟩
  intro e heS hene
  by_contra hcontrib
  have heq :
      e = transverseAxisBlockerExponent x i D :=
    homogeneous_transverse_contributor_eq_blocker
      hhom x i hix e heS hcontrib
  exact hene heq

/-- **Transverse Smith first-wall exclusion.**
At a homogeneous exact collision between the origin and `e_x`, no monomial
`x^(D-1) X_i` with `i != x` can occur in the support. -/
theorem homogeneous_exactAxisCollision_no_transverseBlocker
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (x i : σ)
    (hix : i ≠ x)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x)) :
    transverseAxisBlockerExponent x i D ∉ F.support := by
  intro hsupport
  have hunique :
      IsUniqueGradientContributorAt
        (coordinateAxisPoint (K := K) x)
        F i
        (transverseAxisBlockerExponent x i D) :=
    transverseAxisBlocker_isUniqueGradientContributor
      hhom (by omega) x i hix hsupport
  exact
    homogeneous_exactAxisCollision_uniqueContributor_impossible
      hhom hD x i hcoll
      (transverseAxisBlockerExponent x i D)
      hunique

end

end HC4.Newton
