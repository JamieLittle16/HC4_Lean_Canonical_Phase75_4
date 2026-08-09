import HC4.Newton.SmithFirstWallTransverse
import Mathlib.Tactic

/-!
# Longitudinal Smith first-wall blocker at an axis collision

Phase 93.12 excludes every transverse blocker

    x^(D-1) X_i,  i != x.

The remaining low blocker is the pure longitudinal monomial

    x^D.

At the coordinate-axis point `e_x`, a support monomial can contribute
nontrivially to the `x`-gradient only if differentiating once in `x`
leaves a pure `x`-power.  Therefore the original monomial itself is a pure
`x`-power.  Homogeneity then forces its exponent to be exactly `D`.

Thus `x^D`, if present, is the unique nonzero contributor to the
`x`-gradient at `e_x`, and Phase 93.11's exact-collision theorem excludes
it.

Together with Phase 93.12 this closes all four low Smith blockers:
pure-x, x^(D-1)y, x^(D-1)z, and x^(D-1)w.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The pure longitudinal blocker `x^D`. -/
noncomputable def longitudinalAxisBlockerExponent
    (x : σ)
    (D : ℕ) : σ →₀ ℕ :=
  Finsupp.single x D

/-- **Longitudinal axis contribution classification.**
A homogeneous degree-`D` support monomial contributing nontrivially to the
`x`-gradient at `e_x` is exactly `x^D`. -/
theorem homogeneous_longitudinal_contributor_eq_blocker
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (x : σ)
    (d : σ →₀ ℕ)
    (hd : d ∈ F.support)
    (hcontrib :
      gradientMonomialContributionAt
        (coordinateAxisPoint (K := K) x)
        F x d ≠ 0) :
    d = longitudinalAxisBlockerExponent x D := by
  classical
  have hrem :
      d - (Finsupp.single x 1 : σ →₀ ℕ) =
        Finsupp.single x
          ((d - (Finsupp.single x 1 : σ →₀ ℕ)) x) :=
    derivativeRemainder_eq_single_axis_of_contribution_ne_zero
      x x F d hcontrib
  have hshape :
      d = Finsupp.single x (d x) := by
    apply Finsupp.ext
    intro j
    by_cases hjx : j = x
    · subst j
      simp
    · have hj := congrArg
          (fun r : σ →₀ ℕ => r j) hrem
      have hdj : d j = 0 := by
        simpa [hjx] using hj
      simp [hjx, hdj]
  have hcoeffd :
      MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdeg :
      (Finsupp.weight (fun _ : σ => 1)) d = D :=
    hhom hcoeffd
  rw [hshape] at hdeg
  have hdx :
      d x = D := by
    simpa [Finsupp.weight_single] using hdeg
  unfold longitudinalAxisBlockerExponent
  simpa [hdx] using hshape

/-- Differentiating the pure longitudinal blocker once leaves
`x^(D-1)`. -/
theorem longitudinalAxisBlockerExponent_sub_axis
    (x : σ)
    (D : ℕ) :
    longitudinalAxisBlockerExponent x D -
        (Finsupp.single x 1 : σ →₀ ℕ) =
      Finsupp.single x (D - 1) := by
  classical
  apply Finsupp.ext
  intro j
  by_cases hjx : j = x
  · subst j
    simp [longitudinalAxisBlockerExponent]
  · simp [longitudinalAxisBlockerExponent, hjx]

/-- The pure longitudinal blocker contributes nontrivially to the
`x`-gradient whenever it belongs to the support and `D > 0`. -/
theorem longitudinalAxisBlocker_contribution_ne_zero
    [CharZero K]
    {F : MvPolynomial σ K}
    (x : σ)
    (D : ℕ)
    (hD : 1 ≤ D)
    (hsupport :
      longitudinalAxisBlockerExponent x D ∈ F.support) :
    gradientMonomialContributionAt
        (coordinateAxisPoint (K := K) x)
        F x
        (longitudinalAxisBlockerExponent x D) ≠ 0 := by
  classical
  have hcoeff :
      MvPolynomial.coeff
        (longitudinalAxisBlockerExponent x D) F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hsupport
  have hDne : D ≠ 0 := by
    omega
  rw [gradientMonomialContributionAt_eq]
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero hcoeff ?_
    simp [longitudinalAxisBlockerExponent]
    exact hDne
  · rw [longitudinalAxisBlockerExponent_sub_axis x D]
    have hprod :
        (Finsupp.single x (D - 1) : σ →₀ ℕ).prod
            (fun j e =>
              coordinateAxisPoint (K := K) x j ^ e) = 1 := by
      rw [Finsupp.prod_single_index]
      · simp [coordinateAxisPoint]
      · simp [coordinateAxisPoint]
    rw [hprod]
    exact one_ne_zero

/-- A supported pure longitudinal blocker is the unique nonzero
contributor to the `x`-gradient at `e_x`. -/
theorem longitudinalAxisBlocker_isUniqueGradientContributor
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 1 ≤ D)
    (x : σ)
    (hsupport :
      longitudinalAxisBlockerExponent x D ∈ F.support) :
    IsUniqueGradientContributorAt
      (coordinateAxisPoint (K := K) x)
      F x
      (longitudinalAxisBlockerExponent x D) := by
  refine
    ⟨hsupport,
      longitudinalAxisBlocker_contribution_ne_zero
        x D hD hsupport,
      ?_⟩
  intro e heS hene
  by_contra hcontrib
  have heq :
      e = longitudinalAxisBlockerExponent x D :=
    homogeneous_longitudinal_contributor_eq_blocker
      hhom x e heS hcontrib
  exact hene heq

/-- **Longitudinal Smith first-wall exclusion.**
At a homogeneous exact collision between the origin and `e_x`, the pure
monomial `x^D` cannot occur in the support. -/
theorem homogeneous_exactAxisCollision_no_longitudinalBlocker
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (x : σ)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x)) :
    longitudinalAxisBlockerExponent x D ∉ F.support := by
  intro hsupport
  have hunique :
      IsUniqueGradientContributorAt
        (coordinateAxisPoint (K := K) x)
        F x
        (longitudinalAxisBlockerExponent x D) :=
    longitudinalAxisBlocker_isUniqueGradientContributor
      hhom (by omega) x hsupport
  exact
    homogeneous_exactAxisCollision_uniqueContributor_impossible
      hhom hD x x hcoll
      (longitudinalAxisBlockerExponent x D)
      hunique

/-- Combined low-blocker package: the longitudinal blocker and every
transverse blocker are absent from a homogeneous exact axis collision. -/
theorem homogeneous_exactAxisCollision_no_lowBlockers
    [CharZero K]
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (x : σ)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x)) :
    longitudinalAxisBlockerExponent x D ∉ F.support ∧
      ∀ i, i ≠ x ->
        transverseAxisBlockerExponent x i D ∉ F.support := by
  constructor
  · exact
      homogeneous_exactAxisCollision_no_longitudinalBlocker
        hhom hD x hcoll
  · intro i hix
    exact
      homogeneous_exactAxisCollision_no_transverseBlocker
        hhom hD x i hix hcoll

end

end HC4.Newton
