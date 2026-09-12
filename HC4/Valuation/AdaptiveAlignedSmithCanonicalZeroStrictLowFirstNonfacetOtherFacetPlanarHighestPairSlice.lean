import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarCarrier
import HC4.Polynomial.MaximalSingularInitial
import Mathlib.Tactic

/-!
# A19 highest pair slice of the planar carrier

The planar carrier is a nonzero singular polynomial and retains a support point
of pair degree greater than one.  Taking its maximal exact component for the
pair weight therefore gives a nonzero Hessian-singular slice at pair level
`N>1`.

This is the source-facing version of the highest-slice adapter: unlike an
informal coefficient extraction, it reuses the generic maximal-Hessian-initial
theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

structure QsOtherFacetPlanarHighestPairSlicePackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet)
    (P : QsOtherFacetPlanarCarrierPackage C next) where
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

/-- The support of a highest pair slice lies in the parent planar carrier and
has pair degree exactly its declared level. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.support_parent_and_pairLevel
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    {e : Fin 4 →₀ ℕ} (he : e ∈ S.slice.support) :
    e ∈ P.carrier.support ∧ qsOtherFacetPairDegree next e = S.pairLevel := by
  have hface := HC4.Newton.initialForm_support_isExposedFace
    (qsOtherFacetPairWeight next) S.pairLevel P.carrier S.carrier_pair_bound
  have he' : e ∈
      (HC4.Polynomial.initialForm
        (qsOtherFacetPairWeight next) S.pairLevel P.carrier).support := by
    simpa [S.slice_eq_initialForm] using he
  have hm := hface.mem_iff.mp (by simpa using he')
  refine ⟨by simpa using hm.1, ?_⟩
  rw [finsupp_weight_qsOtherFacetPairWeight] at hm
  exact hm.2

/-- **Highest pair slice.** -/
theorem QsOtherFacetPlanarCarrierPackage.highestPairSlice
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next) :
    Nonempty (QsOtherFacetPlanarHighestPairSlicePackage C next P) := by
  have hcarrier : P.carrier ≠ 0 := by
    rcases P.nonlinear_point with ⟨e, he, _hne, _hp⟩
    exact MvPolynomial.support_nonempty.mp ⟨e, he⟩
  rcases HC4.Polynomial.exists_nonzero_maximal_singular_initial
      (qsOtherFacetPairWeight next) P.carrier hcarrier P.hessian_zero with
    ⟨N, hsliceNe, hbound, hsliceZero⟩
  have hNgt : 1 < N := by
    rcases P.nonlinear_point with ⟨e, he, _hne, hp⟩
    have hle := hbound he
    rw [finsupp_weight_qsOtherFacetPairWeight] at hle
    exact lt_of_lt_of_le hp hle
  let S : MvPolynomial (Fin 4) K :=
    HC4.Polynomial.initialForm (qsOtherFacetPairWeight next) N P.carrier
  exact ⟨{
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
