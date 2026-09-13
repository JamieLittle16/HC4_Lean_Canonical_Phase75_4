import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorFirstVariation
import HC4.Polynomial.AffineEulerTwoRootRigidity
import Mathlib.Tactic

/-!
# A19 two-mode normal form of the first strict-interior profile

The source-honest first-variation theorem gives the affine Euler equation with
adjacent indicial roots `k-1,k`.  The generic affine two-root rigidity theorem
does not require a degree-one hypothesis: after translation to the unique root
of the locked affine form, the coefficient profile is supported only in those
two adjacent powers.

This is the correct replacement for the invalid inference `natDegree phi <= 1`.
The original profile may have many ordinary coefficients (for example an
affine square when `k=2`), but after the canonical translation it has only the
two Euler modes.
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

namespace QsOtherFacetPrLeftVFirstInteriorAffineLayerData

/-- Source support alone bounds the ordinary profile degree by the fixed pair
degree `k`. -/
theorem coefficientProfile_natDegree_le_k
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    A.coefficientProfile.natDegree ≤ A.k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra hcoeff
  have hnmem : n ∈ A.coefficientProfile.support :=
    Polynomial.mem_support_iff.mpr hcoeff
  rcases A.exists_layerExponent_of_coefficientProfile_mem hnmem with
    ⟨e, he, he0⟩
  have hpair := (A.coordinates e he).1
  omega

/-- The first transverse coordinate gives the independent profile-degree
bound `natDegree <= j+1`. -/
theorem coefficientProfile_natDegree_le_j_succ
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    (A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D) :
    A.coefficientProfile.natDegree ≤ A.j + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra hcoeff
  have hnmem : n ∈ A.coefficientProfile.support :=
    Polynomial.mem_support_iff.mpr hcoeff
  rcases A.exists_layerExponent_of_coefficientProfile_mem hnmem with
    ⟨e, he, he0⟩
  have hfirst := (A.coordinates e he).2.1
  omega

end QsOtherFacetPrLeftVFirstInteriorAffineLayerData

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- **Two-mode first-interior normal form.**  If strict-interior support
survives, there is a source-derived first layer whose coefficient profile,
after translating to the root of the literal locked affine form, is supported
only in degrees `k-1` and `k`.

This conclusion is strictly weaker than degree one and is compatible with the
known affine-square test case. -/
theorem exists_firstInteriorAffineLayer_translated_support_twoMode
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
    ∃ A : QsOtherFacetPrLeftVFirstInteriorAffineLayerData D,
      (HC4.Polynomial.translatePolynomial
        (-((MvPolynomial.coeff C.ray.facetExponent P.carrier *
              ((F.locked.ell : K) + 1)) /
            (MvPolynomial.coeff C.ray.outsideExponent P.carrier *
              (F.locked.ell : K))))
        A.coefficientProfile).support ⊆ {A.k - 1, A.k} := by
  rcases D.exists_firstInteriorAffineLayer_affineTwoRootEulerOperator_eq_zero
      hthree houtThree hnot with ⟨A, hode⟩
  refine ⟨A, ?_⟩
  let c : K := MvPolynomial.coeff C.ray.facetExponent P.carrier *
    ((F.locked.ell : K) + 1)
  let d : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier *
    (F.locked.ell : K)
  have hb : MvPolynomial.coeff C.ray.outsideExponent P.carrier ≠ 0 :=
    F.locked.outside_provenance.carrier_coeff_ne
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero hb hellK
  have hs := HC4.Polynomial.translated_support_subset_of_affineTwoRoot
    c d (A.k - 1) A.coefficientProfile hd (by simpa [c, d] using hode)
  have hk : (A.k - 1) + 1 = A.k := by omega
  simpa [c, d, hk] using hs

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
