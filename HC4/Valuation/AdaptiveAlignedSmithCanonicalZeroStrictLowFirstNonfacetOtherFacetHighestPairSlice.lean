import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetNeutralSuperface
import HC4.Polynomial.MaximalSingularInitial
import Mathlib.Tactic

/-!
# A19 highest pair-degree singular slice

The source-honest neutral superface is already Hessian singular and contains a
monomial of pair degree strictly greater than one.  This file applies the
generic maximal-singular-initial theorem to the pair weight.  The resulting
highest pair-degree slice is nonzero, Hessian singular, and has pair level
strictly greater than one.

No determinant coefficient expansion is repeated here: maximal-initial Hessian
compatibility is the single algebraic owner of that argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Highest occupied pair-degree slice of a source-honest neutral superface. -/
structure QsOtherFacetHighestPairSlicePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet)
    (P : QsOtherFacetNeutralSuperfacePackage C next) where
  pairLevel : ℤ
  slice : MvPolynomial (Fin 4) K
  slice_eq_initialForm :
    slice = HC4.Polynomial.initialForm
      (qsOtherFacetPairWeight next) pairLevel P.carrier
  slice_ne_zero : slice ≠ 0
  carrier_pair_bound :
    HC4.Polynomial.IsWeightLE
      (qsOtherFacetPairWeight next) pairLevel P.carrier
  pairLevel_gt_one : 1 < pairLevel
  hessian_zero : HC4.Polynomial.hessianDeterminant slice = 0

/-- **A19 highest-slice singularity adapter.**  A neutral source superface has
a nonzero singular maximal pair-degree component, and the retained strict
source exit forces its pair level to be greater than one. -/
theorem QsOtherFacetNeutralSuperfacePackage.highestPairSlice
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetNeutralSuperfacePackage C next) :
    Nonempty (QsOtherFacetHighestPairSlicePackage C next P) := by
  have hfacetCarrierSet :
      C.ray.facetExponent ∈
        (↑P.carrier.support : Set (Fin 4 →₀ ℕ)) := by
    exact P.ray_support_subset (by simpa using C.ray.facet_mem_face)
  have hfacetCarrier : C.ray.facetExponent ∈ P.carrier.support := by
    simpa using hfacetCarrierSet
  have hcarrier : P.carrier ≠ 0 :=
    MvPolynomial.support_nonempty.mp ⟨C.ray.facetExponent, hfacetCarrier⟩

  rcases HC4.Polynomial.exists_nonzero_maximal_singular_initial
      (qsOtherFacetPairWeight next) P.carrier hcarrier P.hessian_zero with
    ⟨N, hsliceNe, hbound, hsliceZero⟩

  have hNgt : 1 < N := by
    rcases P.nonlinear_pair_exit with ⟨e, he, hePair⟩
    have hle := hbound he
    rw [finsupp_weight_qsOtherFacetPairWeight] at hle
    exact lt_of_lt_of_le hePair hle

  let S : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.initialForm (qsOtherFacetPairWeight next) N P.carrier
  refine ⟨{
    pairLevel := N
    slice := S
    slice_eq_initialForm := by rfl
    slice_ne_zero := by simpa [S] using hsliceNe
    carrier_pair_bound := hbound
    pairLevel_gt_one := hNgt
    hessian_zero := by simpa [S] using hsliceZero
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
