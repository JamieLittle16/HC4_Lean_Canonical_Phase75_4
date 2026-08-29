import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerCausality
import Mathlib.Tactic

/-!
# A19.105: first actual deformation below the locked ray

A19.104b constructs an honest reverse-Rees family whose special fibre is
exactly the balance-free affine ray and whose Hessian determinant is a positive
pure parameter power.  The next staircase datum is therefore canonical: take
the least positive parameter order occurring in that family.

The generic first-layer causality theorem already shows that this order occurs
no later than the determinant clock.  The explicit reverse-Rees coefficient
formula then says more: every monomial in this first layer comes from the
represented determinant-one source and lies on the single parallel weight
level obtained by dropping the ray level by exactly that first order.

Thus the first lower staircase layer is now an honest polynomial face of the
same source filtration.  No assertion is made that it lies on the static ray.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Exact first positive layer of the ray-leading reverse-Rees family. -/
structure QsOtherFacetRayFirstActualLayerPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (R : QsOtherFacetRayReverseReesPackage C) where
  order : ℕ
  order_pos : 0 < order
  order_le_defect :
    order ≤ 4 * R.level - 2 * ∑ i : Fin 4, R.weight i
  order_le_level : order ≤ R.level
  layer : MvPolynomial (Fin 4) K
  layer_eq :
    layer = familyParameterLayer
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) R.bound)
      order
  layer_ne_zero : layer ≠ 0
  support_source :
    ∀ {d : Fin 4 →₀ ℕ}, d ∈ layer.support →
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support
  support_weight_drop :
    ∀ {d : Fin 4 →₀ ℕ}, d ∈ layer.support →
      R.level - Finsupp.weight R.weight d = order
  support_weight_lt_ray :
    ∀ {d : Fin 4 →₀ ℕ}, d ∈ layer.support →
      Finsupp.weight R.weight d < R.level

/-- **A19.105 first honest staircase layer.**  The least positive actual
parameter layer exists, is no later than the pure Hessian clock, and is
supported exactly one fixed positive weight drop below the locked ray. -/
theorem QsOtherFacetRayReverseReesPackage.firstActualLayerPackage
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C) :
    Nonempty (QsOtherFacetRayFirstActualLayerPackage C R) := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let Q : MvPolynomial (Fin 4) (Polynomial K) :=
    reverseWeightedReesFamily R.weight R.level F R.bound
  let j : ℕ := firstPositiveActualParameterOrder Q R.positiveLayer
  let L : MvPolynomial (Fin 4) K := familyParameterLayer Q j

  have hjpos : 0 < j := by
    dsimp [j, Q]
    exact firstPositiveActualParameterOrder_pos
      (reverseWeightedReesFamily R.weight R.level F R.bound)
      R.positiveLayer
  have hjdef :
      j ≤ 4 * R.level - 2 * ∑ i : Fin 4, R.weight i := by
    dsimp [j, Q]
    exact firstPositiveActualParameterOrder_le_hessianDefect
      (reverseWeightedReesFamily R.weight R.level F R.bound)
      R.positiveLayer R.hessianDefect R.defect_pos
  have hLne : L ≠ 0 := by
    dsimp [L, j, Q]
    exact firstPositiveActualParameterLayer_ne_zero
      (reverseWeightedReesFamily R.weight R.level F R.bound)
      R.positiveLayer

  have hsource :
      ∀ {d : Fin 4 →₀ ℕ}, d ∈ L.support → d ∈ F.support := by
    intro d hd
    have hcoeff : MvPolynomial.coeff d L ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    dsimp [L, Q] at hcoeff
    rw [reverseWeightedReesFamily_parameterLayer_coeff] at hcoeff
    by_cases hcond : d ∈ F.support ∧
        R.level - Finsupp.weight R.weight d = j
    · exact hcond.1
    · rw [if_neg hcond] at hcoeff
      exact (hcoeff rfl).elim

  have hdrop :
      ∀ {d : Fin 4 →₀ ℕ}, d ∈ L.support →
        R.level - Finsupp.weight R.weight d = j := by
    intro d hd
    have hcoeff : MvPolynomial.coeff d L ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    dsimp [L, Q] at hcoeff
    rw [reverseWeightedReesFamily_parameterLayer_coeff] at hcoeff
    by_cases hcond : d ∈ F.support ∧
        R.level - Finsupp.weight R.weight d = j
    · exact hcond.2
    · rw [if_neg hcond] at hcoeff
      exact (hcoeff rfl).elim

  have hlt :
      ∀ {d : Fin 4 →₀ ℕ}, d ∈ L.support →
        Finsupp.weight R.weight d < R.level := by
    intro d hd
    have hdF : d ∈ F.support := hsource hd
    have hle := R.bound d hdF
    have heq := hdrop hd
    omega

  have hjlevel : j ≤ R.level := by
    rcases MvPolynomial.support_nonempty.mpr hLne with ⟨d, hd⟩
    have heq := hdrop hd
    omega

  exact ⟨{
    order := j
    order_pos := hjpos
    order_le_defect := hjdef
    order_le_level := hjlevel
    layer := L
    layer_eq := rfl
    layer_ne_zero := hLne
    support_source := by simpa [F] using hsource
    support_weight_drop := hdrop
    support_weight_lt_ray := hlt
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
