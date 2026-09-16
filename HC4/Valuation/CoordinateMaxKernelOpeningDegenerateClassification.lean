import HC4.Valuation.CoordinateMaxKernelOpeningRankFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopLayer
import Mathlib.Tactic

/-!
# Degenerate special-fibre classification for a coordinate-max kernel opening

The nondegenerate complementary `3 x 3` branch of
`CoordinateMaxKernelOpeningRankFrontier` already produces an explicit
first-layer `2 x 2` Hessian minor.  In the complementary low-rank branch we
need only classify the actual special-fibre child.

For a nonzero homogeneous child of degree at least two there is a finite split:

* some `2 x 2` Hessian minor is nonzero, giving literal rank-two geometry
  already on the child; or
* every `2 x 2` Hessian minor vanishes.  The existing homogeneous
  logarithmic-gradient theorem then gives

      child = a * L^m

  for one scalar `a` and one linear form `L`.

This is source-level algebra only.  It does not attach repair progress and it
does not claim that the linear-power opening has already been eliminated.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

/-- Division-free witness that the child Hessian has rank at least two. -/
def ChildHessianRankTwoWitness : Prop :=
  ∃ i j k l : Fin 4,
    HC4.Polynomial.hessian D.child i j *
          HC4.Polynomial.hessian D.child k l -
        HC4.Polynomial.hessian D.child i l *
          HC4.Polynomial.hessian D.child k j ≠ 0

/-- Complete rank-at-most-one Hessian certificate for the child. -/
def ChildHessianRankAtMostOne : Prop :=
  ∀ i j k l : Fin 4,
    HC4.Polynomial.hessian D.child i j *
          HC4.Polynomial.hessian D.child k l -
        HC4.Polynomial.hessian D.child i l *
          HC4.Polynomial.hessian D.child k j = 0

/-- Exhaustive finite determinantal split. -/
theorem childHessian_rankTwoWitness_or_rankAtMostOne :
    D.ChildHessianRankTwoWitness ∨ D.ChildHessianRankAtMostOne := by
  classical
  by_cases hall : D.ChildHessianRankAtMostOne
  · exact Or.inr hall
  · left
    unfold ChildHessianRankAtMostOne at hall
    simp only [not_forall] at hall
    rcases hall with ⟨i, hi⟩
    rcases hi with ⟨j, hj⟩
    rcases hj with ⟨k, hk⟩
    rcases hk with ⟨l, hl⟩
    exact ⟨i, j, k, l, hl⟩

/-- Homogeneity of the ambient source descends to the exact child because the
child support is literally a subset of the source support. -/
theorem child_isHomogeneous
    {m : ℕ}
    (hhom : F.IsHomogeneous m) :
    D.child.IsHomogeneous m := by
  intro d hd
  have hdmem : d ∈ D.child.support := MvPolynomial.mem_support_iff.mpr hd
  have hdF : d ∈ F.support := D.child_support_subset_source hdmem
  exact hhom (MvPolynomial.mem_support_iff.mp hdF)

/-- All Hessian `2 x 2` minors zero on a nonzero homogeneous child force the
exact scalar-linear-power normal form, reusing the already-green four-variable
homogeneous rank-one classification. -/
theorem child_linearPower_of_rankAtMostOne
    {m : ℕ}
    (hhom : F.IsHomogeneous m)
    (hm : 2 ≤ m)
    (hall : D.ChildHessianRankAtMostOne) :
    ∃ (a : K) (c : Fin 4 → K),
      D.child =
        MvPolynomial.C a * (gradientRatioLinearForm c) ^ m := by
  have hchildHom : D.child.IsHomogeneous m := D.child_isHomogeneous hhom
  rcases rankOneHomogeneousLogGradientData_of_allMinors
      D.child m hchildHom D.child_ne_zero hm hall with ⟨L⟩
  rcases rankOneHomogeneousLogGradientData_four_global L with ⟨c, hc⟩
  rcases homogeneous_eq_C_mul_gradientRatioLinearForm_pow
      m D.child hchildHom (by omega)
      L.pivot L.pivot_ne_zero c hc with ⟨a, ha⟩
  exact ⟨a, c, ha⟩

/-- Exact low-rank child normal form retained after the finite rank split. -/
structure ChildLinearPowerData
    (m : ℕ) where
  coefficient : K
  ratio : Fin 4 → K
  eq_power :
    D.child = MvPolynomial.C coefficient *
      (gradientRatioLinearForm ratio) ^ m

/-- **Degenerate child frontier.**  There is no unclassified Hessian-rank
branch: either literal rank-two geometry is already present on the child, or
the child is exactly a scalar power of one linear form. -/
theorem child_rankTwo_or_linearPower
    {m : ℕ}
    (hhom : F.IsHomogeneous m)
    (hm : 2 ≤ m) :
    D.ChildHessianRankTwoWitness ∨
      Nonempty (D.ChildLinearPowerData m) := by
  rcases D.childHessian_rankTwoWitness_or_rankAtMostOne with htwo | hall
  · exact Or.inl htwo
  · rcases D.child_linearPower_of_rankAtMostOne hhom hm hall with ⟨a, c, hpower⟩
    exact Or.inr ⟨{
      coefficient := a
      ratio := c
      eq_power := hpower
    }⟩

end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
