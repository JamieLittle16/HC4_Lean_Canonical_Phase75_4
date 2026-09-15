import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorAffineCoordinates
import Mathlib.Tactic

/-!
# A19 source-honest affine package for the first strict-interior layer

The preceding file expands the quotient invariants into literal source
coordinates.  This file packages those equations and extracts the honest
one-variable coefficient profile indexed by coordinate `0`.

The essential point is that coordinate `0` is injective on the selected
layer: once two supported exponents have the same longitudinal coordinate,
the three affine equations force all four source exponents to agree.  Hence
collecting coefficients by coordinate `0` introduces no cancellation.
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

/-- Exact source-facing data of the least positive strict-interior layer. -/
structure QsOtherFacetPrLeftVFirstInteriorAffineLayerData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) where
  k : ℕ
  j : ℕ
  k_gt_one : 1 < k
  k_lt_highest : k < F.highest.n
  j_pos : 0 < j
  j_lt_locked : j < F.locked.ell
  coordinates :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
      e 0 + e 1 = k ∧
      e 0 + e 2 = j + 1 ∧
      F.V * e 0 + e 3 = F.V * (k + j)
  coefficient_eq_carrier :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) =
        MvPolynomial.coeff e P.carrier

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- The live strict-interior branch canonically produces the affine-layer
package, with no additional assumption on profile degree. -/
theorem exists_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) := by
  rcases D.exists_firstPositiveLayer_strictInterior_affineCoordinates
      hthree houtThree hnot with
    ⟨k, j, hkgt, hklt, hjpos, hjlt, hall⟩
  exact ⟨{
    k := k
    j := j
    k_gt_one := hkgt
    k_lt_highest := hklt
    j_pos := hjpos
    j_lt_locked := hjlt
    coordinates := by
      intro e he
      exact (hall e he).1
    coefficient_eq_carrier := by
      intro e he
      exact (hall e he).2.2.2
  }⟩

/-- Coordinate `0` is a genuine lattice parameter on the selected layer. -/
theorem eq_of_zeroCoordinate_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hzero : e 0 = f 0) : e = f := by
  rcases A.coordinates e he with ⟨he1, he2, he3⟩
  rcases A.coordinates f hf with ⟨hf1, hf2, hf3⟩
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact hzero
  · omega
  · omega
  · have hsum : F.V * e 0 + e 3 = F.V * e 0 + f 3 := by
      calc
        F.V * e 0 + e 3 = F.V * (A.k + A.j) := he3
        _ = F.V * f 0 + f 3 := hf3.symm
    exact Nat.add_left_cancel hsum

/-- The coefficient profile of the first layer, indexed by its honest
coordinate-zero exponent. -/
noncomputable def coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (_A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) : Polynomial K :=
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  ∑ e ∈ L.support, Polynomial.monomial (e 0) (MvPolynomial.coeff e L)

/-- Because coordinate `0` is injective on support, the extracted profile
retains each layer coefficient literally. -/
theorem coeff_coefficientProfile_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    A.coefficientProfile.coeff (e 0) =
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) := by
  classical
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  change
    (∑ f ∈ L.support,
      Polynomial.monomial (f 0) (MvPolynomial.coeff f L)).coeff (e 0) =
      MvPolynomial.coeff e L
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hz : f 0 ≠ e 0 := by
      intro hcoord
      apply hfe
      exact A.eq_of_zeroCoordinate_eq hf he hcoord
    simp [Polynomial.coeff_monomial, hz]
  · intro hnot
    exact (hnot he).elim

/-- The extracted first-layer profile is nonzero. -/
theorem coefficientProfile_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    A.coefficientProfile ≠ 0 := by
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  have hL : L ≠ 0 := by
    dsimp [L]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.hasPositiveLayer
  rcases MvPolynomial.support_nonempty.mpr hL with ⟨e, he⟩
  have hc : MvPolynomial.coeff e L ≠ 0 := MvPolynomial.mem_support_iff.mp he
  intro hz
  have hpz : A.coefficientProfile.coeff (e 0) = 0 := by
    simpa using congrArg (fun p : Polynomial K => p.coeff (e 0)) hz
  have hp := A.coeff_coefficientProfile_of_mem (e := e) (by simpa [L] using he)
  rw [hp] at hpz
  exact hc (by simpa [L] using hpz)

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
