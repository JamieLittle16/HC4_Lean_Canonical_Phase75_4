import HC4.Newton.SmithFiniteBalanceClosure
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Exact homogeneous collision and unique first-wall contributors

The remaining Smith first-wall argument should be combinatorial.

This file factors out the generic polynomial statement used there.

For a polynomial `F`, a point `p`, and a coordinate `i`, define the
gradient component

    eval p (pderiv i F).

We also define the contribution of one support monomial `d` to that
evaluated partial derivative.  The full component is the finite sum of
these monomial contributions.

If `F` is homogeneous of degree `D >= 2`, every partial derivative is
homogeneous of positive degree, hence its value at the origin is zero.
Therefore an exact gradient collision between the origin and any second
point forces every gradient component at the second point to vanish.

Consequently, if at a first wall one support monomial is the unique
nonzero contributor to a component of the gradient at the collision point,
that wall is impossible.

The hard Smith file therefore only has to prove the finite
enumeration/uniqueness statements for the low blockers.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- One component of the gradient of an `MvPolynomial`, evaluated at a
point. -/
def mvGradientComponentAt
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ) : K :=
  MvPolynomial.eval point (MvPolynomial.pderiv i F)

/-- The full evaluated gradient. -/
def mvGradientAt
    (point : σ → K)
    (F : MvPolynomial σ K) : σ → K :=
  fun i => mvGradientComponentAt point F i

/-- The coordinate-axis point with value `1` in coordinate `x` and `0`
elsewhere. -/
noncomputable def coordinateAxisPoint
    (x : σ) : σ → K := by
  classical
  exact fun i => if i = x then 1 else 0

/-- Exact equality of the evaluated gradients at two points. -/
def HasExactGradientCollision
    (F : MvPolynomial σ K)
    (p q : σ → K) : Prop :=
  ∀ i, mvGradientComponentAt p F i =
    mvGradientComponentAt q F i

/-- Contribution of one support monomial to one evaluated gradient
component.  It is defined through the actual derivative and evaluation,
so no coefficient formula is hidden in the uniqueness predicate. -/
def gradientMonomialContributionAt
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ) : K :=
  MvPolynomial.eval point
    (MvPolynomial.pderiv i
      (MvPolynomial.monomial d
        (MvPolynomial.coeff d F)))

/-- Expanded coefficient formula for a single gradient contribution. -/
theorem gradientMonomialContributionAt_eq
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ) :
    gradientMonomialContributionAt point F i d =
      (MvPolynomial.coeff d F * ((d i : ℕ) : K)) *
        (d - Finsupp.single i 1).prod
          (fun j e => point j ^ e) := by
  classical
  simp [gradientMonomialContributionAt,
    MvPolynomial.pderiv_monomial,
    MvPolynomial.eval_monomial]

/-- The evaluated partial derivative is the finite sum of the
contributions of the support monomials of `F`. -/
theorem mvGradientComponentAt_eq_sum_support
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ) :
    mvGradientComponentAt point F i =
      F.support.sum
        (fun d =>
          gradientMonomialContributionAt point F i d) := by
  classical
  unfold mvGradientComponentAt
  calc
    MvPolynomial.eval point (MvPolynomial.pderiv i F) =
        MvPolynomial.eval point
          (MvPolynomial.pderiv i
            (F.support.sum
              (fun d =>
                MvPolynomial.monomial d
                  (MvPolynomial.coeff d F)))) := by
      exact congrArg
        (fun P : MvPolynomial σ K =>
          MvPolynomial.eval point
            (MvPolynomial.pderiv i P))
        F.as_sum
    _ = F.support.sum
        (fun d =>
          gradientMonomialContributionAt point F i d) := by
      rw [map_sum
        (MvPolynomial.pderiv i)
        (fun d =>
          MvPolynomial.monomial d
            (MvPolynomial.coeff d F))
        F.support]
      rw [map_sum
        (MvPolynomial.eval point)
        (fun d =>
          MvPolynomial.pderiv i
            (MvPolynomial.monomial d
              (MvPolynomial.coeff d F)))
        F.support]
      rfl

/-- A support monomial is the unique nonzero contributor to a chosen
evaluated gradient component. -/
def IsUniqueGradientContributorAt
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ) : Prop :=
  d ∈ F.support ∧
    gradientMonomialContributionAt point F i d ≠ 0 ∧
    ∀ e ∈ F.support,
      e ≠ d ->
        gradientMonomialContributionAt point F i e = 0

/-- If a support monomial is the unique contributor, the whole evaluated
gradient component equals that monomial's contribution. -/
theorem mvGradientComponentAt_eq_uniqueContributor
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ)
    (hunique :
      IsUniqueGradientContributorAt point F i d) :
    mvGradientComponentAt point F i =
      gradientMonomialContributionAt point F i d := by
  classical
  rw [mvGradientComponentAt_eq_sum_support]
  apply Finset.sum_eq_single d
  · intro e heS hed
    exact hunique.2.2 e heS hed
  · intro hdnot
    exact False.elim (hdnot hunique.1)

/-- A homogeneous polynomial of degree at least two has zero gradient at
the origin. -/
theorem homogeneous_gradient_zero_at_origin
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D) :
    ∀ i,
      mvGradientComponentAt
        (fun _ => (0 : K)) F i = 0 := by
  intro i
  unfold mvGradientComponentAt
  rw [MvPolynomial.eval_zero']
  change
    MvPolynomial.coeff 0
      (MvPolynomial.pderiv i F) = 0
  have hp :
      (MvPolynomial.pderiv i F).IsHomogeneous
        (D - 1) :=
    hhom.pderiv
  apply hp.coeff_eq_zero
  have hpos : 0 < D - 1 := by
    omega
  simpa using (ne_of_lt hpos)

/-- **Homogeneous exact collision gradient.**
If a degree-`D >= 2` homogeneous polynomial has equal gradients at the
origin and a point `q`, then its gradient at `q` is zero. -/
theorem homogeneous_exactCollision_gradient_zero
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (q : σ → K)
    (hcoll :
      HasExactGradientCollision
        F (fun _ => (0 : K)) q) :
    ∀ i, mvGradientComponentAt q F i = 0 := by
  intro i
  rw [← hcoll i]
  exact
    homogeneous_gradient_zero_at_origin
      hhom hD i

/-- Axis-point specialization used by the Smith first-wall argument. -/
theorem homogeneous_exactAxisCollision_gradient_zero
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
    ∀ i,
      mvGradientComponentAt
        (coordinateAxisPoint (K := K) x)
        F i = 0 := by
  exact
    homogeneous_exactCollision_gradient_zero
      hhom hD
      (coordinateAxisPoint (K := K) x)
      hcoll

/-- **Finite unique-wall exclusion.**
A zero evaluated gradient component cannot have a unique nonzero support
contributor. -/
theorem uniqueGradientContributor_impossible
    (point : σ → K)
    (F : MvPolynomial σ K)
    (i : σ)
    (d : σ →₀ ℕ)
    (hzero :
      mvGradientComponentAt point F i = 0)
    (hunique :
      IsUniqueGradientContributorAt point F i d) :
    False := by
  have heq :=
    mvGradientComponentAt_eq_uniqueContributor
      point F i d hunique
  have hnonzero := hunique.2.1
  apply hnonzero
  rw [← heq, hzero]

/-- **Exact-collision first-wall exclusion.**
For a homogeneous degree-`D >= 2` exact collision, any monomial proved to
be the unique nonzero contributor to one gradient component at the
collision point yields a contradiction.

This is the generic theorem that `SmithFirstWall` should invoke after its
directional recurrence/enumeration proves uniqueness of a candidate low
blocker. -/
theorem homogeneous_exactCollision_uniqueContributor_impossible
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (q : σ → K)
    (hcoll :
      HasExactGradientCollision
        F (fun _ => (0 : K)) q)
    (i : σ)
    (d : σ →₀ ℕ)
    (hunique :
      IsUniqueGradientContributorAt q F i d) :
    False := by
  have hzero :
      mvGradientComponentAt q F i = 0 :=
    homogeneous_exactCollision_gradient_zero
      hhom hD q hcoll i
  exact
    uniqueGradientContributor_impossible
      q F i d hzero hunique

/-- Axis-point form of the exact-collision first-wall exclusion. -/
theorem homogeneous_exactAxisCollision_uniqueContributor_impossible
    {F : MvPolynomial σ K}
    {D : ℕ}
    (hhom : F.IsHomogeneous D)
    (hD : 2 ≤ D)
    (x i : σ)
    (hcoll :
      HasExactGradientCollision
        F
        (fun _ => (0 : K))
        (coordinateAxisPoint (K := K) x))
    (d : σ →₀ ℕ)
    (hunique :
      IsUniqueGradientContributorAt
        (coordinateAxisPoint (K := K) x)
        F i d) :
    False := by
  exact
    homogeneous_exactCollision_uniqueContributor_impossible
      hhom hD
      (coordinateAxisPoint (K := K) x)
      hcoll i d hunique

end

end HC4.Newton
