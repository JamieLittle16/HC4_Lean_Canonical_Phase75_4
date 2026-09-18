import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitAxis
import Mathlib.Tactic

/-!
# The first positive total-deficit layer is one honest roof monomial

The rooted first-deficit axis theorem says that the least positive
total-deficit binary face lies entirely on one coordinate axis.  The binary
specialisation is coefficient-faithful on the first source layer, so the same
axis statement holds before specialisation.

Every source exponent in that layer has total deficit equal to the selected
first order.  Hence one deficit coordinate is zero and the other is fixed.
The source-honest deficit projection is injective on the planar carrier, so
there can be only one source monomial in the whole first layer.

No new Rees clock or repair transition is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- Every honest first-layer source monomial survives in the binary deficit
specialisation. -/
theorem firstDeficitLayer_binaryExponent_mem
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ G.firstDeficitLayer.support) :
    HC4.Polynomial.binaryDeficitExponent e ∈ G.firstDeficitBinaryFace.support := by
  have hcoeff :=
    HC4.Polynomial.coeff_centralDeficitBinarySpecialisation_of_mem
      G.firstDeficitLayer he
      (by
        intro f hf hproj
        exact G.firstDeficitLayer_deficit_injective
          hthree houtThree he hf hproj)
  have hsource : MvPolynomial.coeff e G.firstDeficitLayer ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  apply MvPolynomial.mem_support_iff.mpr
  unfold firstDeficitBinaryFace
  rw [hcoeff]
  exact hsource

/-- The axis alternative descends from the binary first face to the actual
source layer. -/
theorem firstDeficitLayer_axis_support
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∀ e ∈ G.firstDeficitLayer.support, e 2 = 0) ∨
      (∀ e ∈ G.firstDeficitLayer.support, e 1 = 0) := by
  rcases G.firstDeficitBinaryFace_axis_support hthree houtThree with
    hzero | hone
  · left
    intro e he
    have hmem := G.firstDeficitLayer_binaryExponent_mem
      hthree houtThree he
    have h := hzero (HC4.Polynomial.binaryDeficitExponent e) hmem
    simpa using h
  · right
    intro e he
    have hmem := G.firstDeficitLayer_binaryExponent_mem
      hthree houtThree he
    have h := hone (HC4.Polynomial.binaryDeficitExponent e) hmem
    simpa using h

/-- The first positive total-deficit order is genuinely nonlinear.  A
unit deficit would contradict the exact staircase chord relative to the
central source monomial. -/
theorem firstDeficitOrder_two_le
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    2 ≤ G.firstDeficitOrder := by
  by_contra hnot
  have hD : G.firstDeficitOrder = 1 := by
    have hpos := G.firstDeficitOrder_pos
    omega
  rcases MvPolynomial.support_nonempty.mpr G.firstDeficitLayer_ne_zero with
    ⟨e, he⟩
  have heData := G.firstDeficitLayer_support he
  have hc :=
    F.support_deficit_chord hthree houtThree G.central_mem
  have heq :=
    F.support_deficit_chord hthree houtThree heData.1
  have hc0 :
      (0 : ℤ) =
        (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - 1) +
          ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
            (1 - (G.central 0 : ℤ)) := by
    simpa [G.central_one_zero, G.central_two_zero] using hc
  have hunit : e 1 + e 2 = 1 := by
    simpa [hD] using heData.2
  exact no_unit_total_deficit_from_central_staircase_chord
    F.highest.n_two_le F.locked.ell_pos hc0 heq hunit

/-- **First total-deficit layer singleton.**

The first positive layer is one honest roof monomial.  In the first
alternative its source deficits are `(D,0)`; in the second they are
`(0,D)`, where `D` is the exact first deficit order. -/
theorem firstDeficitLayer_singleton_axis
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ e : Fin 4 →₀ ℕ,
        e ∈ G.firstDeficitLayer.support ∧
        e 1 = G.firstDeficitOrder ∧
        e 2 = 0 ∧
        ∀ f ∈ G.firstDeficitLayer.support, f = e) ∨
      (∃ e : Fin 4 →₀ ℕ,
        e ∈ G.firstDeficitLayer.support ∧
        e 1 = 0 ∧
        e 2 = G.firstDeficitOrder ∧
        ∀ f ∈ G.firstDeficitLayer.support, f = e) := by
  rcases MvPolynomial.support_nonempty.mpr G.firstDeficitLayer_ne_zero with
    ⟨e, he⟩
  rcases G.firstDeficitLayer_axis_support hthree houtThree with
    htwo | hone
  · left
    have heData := G.firstDeficitLayer_support he
    have he2 : e 2 = 0 := htwo e he
    have he1 : e 1 = G.firstDeficitOrder := by omega
    refine ⟨e, he, he1, he2, ?_⟩
    intro f hf
    have hfData := G.firstDeficitLayer_support hf
    have hf2 : f 2 = 0 := htwo f hf
    have hf1 : f 1 = G.firstDeficitOrder := by omega
    exact F.support_eq_of_deficits_eq
      hthree houtThree hfData.1 heData.1
      (by omega) (by omega)
  · right
    have heData := G.firstDeficitLayer_support he
    have he1 : e 1 = 0 := hone e he
    have he2 : e 2 = G.firstDeficitOrder := by omega
    refine ⟨e, he, he1, he2, ?_⟩
    intro f hf
    have hfData := G.firstDeficitLayer_support hf
    have hf1 : f 1 = 0 := hone f hf
    have hf2 : f 2 = G.firstDeficitOrder := by omega
    exact F.support_eq_of_deficits_eq
      hthree houtThree hfData.1 heData.1
      (by omega) (by omega)

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
