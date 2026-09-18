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

/-- Literal monomial form of the first positive total-deficit source layer.

This keeps the honest source coefficient together with the axis exponent, so
later Hessian coefficient calculations do not have to reconstruct singleton
support again. -/
theorem firstDeficitLayer_eq_monomial_axis
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ (e : Fin 4 →₀ ℕ) (A : K),
        A ≠ 0 ∧
        G.firstDeficitLayer = MvPolynomial.monomial e A ∧
        e 1 = G.firstDeficitOrder ∧ e 2 = 0) ∨
      (∃ (e : Fin 4 →₀ ℕ) (A : K),
        A ≠ 0 ∧
        G.firstDeficitLayer = MvPolynomial.monomial e A ∧
        e 1 = 0 ∧ e 2 = G.firstDeficitOrder) := by
  rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
    hleft | hright
  · rcases hleft with ⟨e, he, he1, he2, huniq⟩
    let A := MvPolynomial.coeff e G.firstDeficitLayer
    have hA : A ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have hmono :
        G.firstDeficitLayer = MvPolynomial.monomial e A := by
      apply MvPolynomial.ext
      intro f
      by_cases hfe : f = e
      · subst f
        simp [A]
      · have hf0 : MvPolynomial.coeff f G.firstDeficitLayer = 0 := by
          by_contra hf
          have hfmem : f ∈ G.firstDeficitLayer.support :=
            MvPolynomial.mem_support_iff.mpr hf
          exact hfe (huniq f hfmem)
        rw [hf0]
        simp [hfe]
    exact Or.inl ⟨e, A, hA, hmono, he1, he2⟩
  · rcases hright with ⟨e, he, he1, he2, huniq⟩
    let A := MvPolynomial.coeff e G.firstDeficitLayer
    have hA : A ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have hmono :
        G.firstDeficitLayer = MvPolynomial.monomial e A := by
      apply MvPolynomial.ext
      intro f
      by_cases hfe : f = e
      · subst f
        simp [A]
      · have hf0 : MvPolynomial.coeff f G.firstDeficitLayer = 0 := by
          by_contra hf
          have hfmem : f ∈ G.firstDeficitLayer.support :=
            MvPolynomial.mem_support_iff.mpr hf
          exact hfe (huniq f hfmem)
        rw [hf0]
        simp [hfe]
    exact Or.inr ⟨e, A, hA, hmono, he1, he2⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
