import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitPrimitiveOpposite
import Mathlib.Tactic

/-!
# Exact source shape of the least opposite-opening layer

`FirstDeficitPrimitiveOppositeOpening` already proves that the selected least
later opening uses the missing source coordinate to exponent exactly one.

The staggered diagonal cancellation applies to every monomial in the exact \`j\)-layer:
no exponent there can use the missing coordinate twice.  Since total-deficit
order is exactly \`j\`, the only possible deficit pairs are the selected
opposite point and the adjacent axis point.  The already-verified
adjacent-deficit exclusion rules out the latter.  Hence the whole \`j\)-layer is
one honest source monomial.

This retains the source exponent and coefficient for the next Schur/reflection
coefficient calculation.
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

private theorem leftOppositeLayer_secondDerivative_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    MvPolynomial.pderiv (2 : Fin 4)
      (MvPolynomial.pderiv (2 : Fin 4)
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))) = 0 := by
  have hz :=
    G.firstDeficitLeftStaggeredBlock_kernelDiagonal_eq_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
      hop hop2 hstrict hminimal
  have hz' :
      (parameterFirstHessian P.centralDeficitFamily
        (2 : Fin 4) (2 : Fin 4)).coeff
          (opposite 1 + opposite 2) = 0 := by
    simpa [firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hz
  rw [parameterFirstHessian_coeff] at hz'
  simpa [HC4.Polynomial.hessian_apply] using hz'

private theorem rightOppositeLayer_secondDerivative_eq_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    MvPolynomial.pderiv (1 : Fin 4)
      (MvPolynomial.pderiv (1 : Fin 4)
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))) = 0 := by
  have hz :=
    G.firstDeficitRightStaggeredBlock_kernelDiagonal_eq_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal
  have hz' :
      (parameterFirstHessian P.centralDeficitFamily
        (1 : Fin 4) (1 : Fin 4)).coeff
          (opposite 1 + opposite 2) = 0 := by
    simpa [firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hz
  rw [parameterFirstHessian_coeff] at hz'
  simpa [HC4.Polynomial.hessian_apply] using hz'

/-- The complete least opposite layer is a singleton in the left orientation. -/
theorem firstDeficitLeftOpposite_layer_singleton
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2one : opposite 2 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∀ f ∈ (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2)).support,
      f = opposite := by
  have hop2 : 0 < opposite 2 := by omega
  have hsecond :=
    G.leftOppositeLayer_secondDerivative_eq_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
      hop hop2 hstrict hminimal
  intro f hf
  have hfsource :=
    (P.centralDeficitFamily_layer_mem_iff
      (opposite 1 + opposite 2) f).1 hf
  have hf2le : f 2 ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ f 2 := by omega
    exact
      (HC4.Valuation.pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (2 : Fin 4)
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))
        f hf htwo) hsecond
  rcases Nat.eq_zero_or_pos (f 2) with hf2zero | hf2pos
  · have hf1 :
        f 1 = opposite 1 + 1 := by
      omega
    have hop2succ : opposite 2 = f 2 + 1 := by
      omega
    exact (F.no_adjacent_deficits hthree houtThree
      hop hfsource.1 hf1 hop2succ).elim
  · have hf2one : f 2 = 1 := by omega
    have hf1eq : f 1 = opposite 1 := by omega
    exact F.support_eq_of_deficits_eq
      hthree houtThree hfsource.1 hop hf1eq
      (by rw [hf2one, hop2one])

/-- Right-oriented singleton opposite layer. -/
theorem firstDeficitRightOpposite_layer_singleton
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1one : opposite 1 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∀ f ∈ (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2)).support,
      f = opposite := by
  have hop1 : 0 < opposite 1 := by omega
  have hsecond :=
    G.rightOppositeLayer_secondDerivative_eq_zero
      hthree houtThree hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal
  intro f hf
  have hfsource :=
    (P.centralDeficitFamily_layer_mem_iff
      (opposite 1 + opposite 2) f).1 hf
  have hf1le : f 1 ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ f 1 := by omega
    exact
      (HC4.Valuation.pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (1 : Fin 4)
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2))
        f hf htwo) hsecond
  rcases Nat.eq_zero_or_pos (f 1) with hf1zero | hf1pos
  · have hop1succ : opposite 1 = f 1 + 1 := by
      omega
    have hf2 :
        f 2 = opposite 2 + 1 := by
      omega
    exact (F.no_adjacent_deficits hthree houtThree
      hfsource.1 hop hop1succ hf2).elim
  · have hf1one : f 1 = 1 := by omega
    have hf2eq : f 2 = opposite 2 := by omega
    exact F.support_eq_of_deficits_eq
      hthree houtThree hfsource.1 hop
      (by rw [hf1one, hop1one]) hf2eq

/-- Literal monomial reconstruction of the left least opposite layer. -/
theorem firstDeficitLeftOpposite_layer_eq_monomial
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2one : opposite 2 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∃ B : K, B ≠ 0 ∧
      familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2) =
        MvPolynomial.monomial opposite B := by
  let L :=
    familyParameterLayer P.centralDeficitFamily
      (opposite 1 + opposite 2)
  have hopLayer : opposite ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  let B := MvPolynomial.coeff opposite L
  have hB : B ≠ 0 := MvPolynomial.mem_support_iff.mp hopLayer
  refine ⟨B, hB, ?_⟩
  apply MvPolynomial.ext
  intro f
  by_cases hfo : f = opposite
  · subst f
    simp [B]
  · have hf0 : MvPolynomial.coeff f L = 0 := by
      by_contra hf
      have hfmem : f ∈ L.support :=
        MvPolynomial.mem_support_iff.mpr hf
      exact hfo (G.firstDeficitLeftOpposite_layer_singleton
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop2one hstrict hminimal f hfmem)
    rw [hf0, MvPolynomial.coeff_monomial]
    simp [hfo, Ne.symm hfo]

/-- Literal monomial reconstruction of the right least opposite layer. -/
theorem firstDeficitRightOpposite_layer_eq_monomial
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1one : opposite 1 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    ∃ B : K, B ≠ 0 ∧
      familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2) =
        MvPolynomial.monomial opposite B := by
  let L :=
    familyParameterLayer P.centralDeficitFamily
      (opposite 1 + opposite 2)
  have hopLayer : opposite ∈ L.support := by
    dsimp [L]
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  let B := MvPolynomial.coeff opposite L
  have hB : B ≠ 0 := MvPolynomial.mem_support_iff.mp hopLayer
  refine ⟨B, hB, ?_⟩
  apply MvPolynomial.ext
  intro f
  by_cases hfo : f = opposite
  · subst f
    simp [B]
  · have hf0 : MvPolynomial.coeff f L = 0 := by
      by_contra hf
      have hfmem : f ∈ L.support :=
        MvPolynomial.mem_support_iff.mpr hf
      exact hfo (G.firstDeficitRightOpposite_layer_singleton
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop1one hstrict hminimal f hfmem)
    rw [hf0, MvPolynomial.coeff_monomial]
    simp [hfo, Ne.symm hfo]

/-- In the left orientation the exact opposite layer opens the specific
mixed Hessian entry between the first-deficit axis and the missing coordinate. -/
theorem firstDeficitLeftOpposite_mixedCoeff_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hop2one : opposite 2 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2) :
    G.firstDeficitLeftStaggeredBlock.s.coeff
        (opposite 1 + opposite 2) ≠ 0 := by
  have hq2 : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  have hop1pos : 0 < opposite 1 := by omega
  have hop2pos : 0 < opposite 2 := by omega
  have hopLayer :
      opposite ∈
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  have hmixed :
      MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))) ≠ 0 :=
    HC4.Polynomial.pderiv_pderiv_ne_zero_of_support_two_positive
      (1 : Fin 4) 2 (by decide)
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2))
      opposite hopLayer hop1pos hop2pos
  unfold firstDeficitLeftStaggeredBlock
    firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [parameterFirstHessian_coeff]
  simpa [HC4.Polynomial.hessian_apply] using hmixed

/-- Right-oriented mirror of the exact mixed opening. -/
theorem firstDeficitRightOpposite_mixedCoeff_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hop1one : opposite 1 = 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2) :
    G.firstDeficitRightStaggeredBlock.s.coeff
        (opposite 1 + opposite 2) ≠ 0 := by
  have hq2 : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  have hop1pos : 0 < opposite 1 := by omega
  have hop2pos : 0 < opposite 2 := by omega
  have hopLayer :
      opposite ∈
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  have hmixed :
      MvPolynomial.pderiv (1 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2))) ≠ 0 :=
    HC4.Polynomial.pderiv_pderiv_ne_zero_of_support_two_positive
      (2 : Fin 4) 1 (by decide)
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2))
      opposite hopLayer hop2pos hop1pos
  unfold firstDeficitRightStaggeredBlock
    firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [parameterFirstHessian_coeff]
  simpa [HC4.Polynomial.hessian_apply] using hmixed

/-- Provenance-rich exact shape of the least later opposite-opening layer. -/
inductive FirstDeficitOppositeLayerGeometry
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) : Prop
  | left
      (first opposite : Fin 4 →₀ ℕ) (B : K)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = G.firstDeficitOrder)
      (first_two : first 2 = 0)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
      (coefficient_ne_zero : B ≠ 0)
      (layer_eq :
        familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2) =
          MvPolynomial.monomial opposite B)
      (mixed_coeff_ne_zero :
        G.firstDeficitLeftStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0)
  | right
      (first opposite : Fin 4 →₀ ℕ) (B : K)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = G.firstDeficitOrder)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
      (coefficient_ne_zero : B ≠ 0)
      (layer_eq :
        familyParameterLayer P.centralDeficitFamily
            (opposite 1 + opposite 2) =
          MvPolynomial.monomial opposite B)
      (mixed_coeff_ne_zero :
        G.firstDeficitRightStaggeredBlock.s.coeff
          (opposite 1 + opposite 2) ≠ 0)

/-- **Exact least-opposite source layer.**  The first later opening of the
missing coordinate is one honest monomial and is linear in that coordinate. -/
theorem firstDeficit_oppositeLayerGeometry
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitOppositeLayerGeometry := by
  rcases G.firstDeficit_primitiveOppositeOpening hthree houtThree with ⟨O⟩
  cases O with
  | left first opposite hfirst hfirst1 hfirst2 huniq
      hop hop2one hstrict hminimal =>
      rcases G.firstDeficitLeftOpposite_layer_eq_monomial
          hthree houtThree hfirst hfirst1 hfirst2 huniq
          hop hop2one hstrict hminimal with
        ⟨B, hB, hlayer⟩
      have hmixed :=
        G.firstDeficitLeftOpposite_mixedCoeff_ne_zero
          hthree houtThree hop hop2one hstrict
      exact .left first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop2one
        hstrict hminimal hB hlayer hmixed
  | right first opposite hfirst hfirst1 hfirst2 huniq
      hop hop1one hstrict hminimal =>
      rcases G.firstDeficitRightOpposite_layer_eq_monomial
          hthree houtThree hfirst hfirst1 hfirst2 huniq
          hop hop1one hstrict hminimal with
        ⟨B, hB, hlayer⟩
      have hmixed :=
        G.firstDeficitRightOpposite_mixedCoeff_ne_zero
          hthree houtThree hop hop1one hstrict
      exact .right first opposite B
        hfirst hfirst1 hfirst2 huniq hop hop1one
        hstrict hminimal hB hlayer hmixed

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
