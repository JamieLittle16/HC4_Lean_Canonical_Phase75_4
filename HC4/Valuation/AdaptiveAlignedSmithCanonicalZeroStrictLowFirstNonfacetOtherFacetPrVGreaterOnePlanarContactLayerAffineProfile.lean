import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerAffineCoordinates
import Mathlib.Tactic

/-!
# A19 source-honest affine profiles for arbitrary planar-contact layers

The first-interior branch already packages the least positive layer as an
affine line with a one-variable coefficient profile.  The all-depth Hessian
argument needs that package uniformly for every nonzero exact parameter layer.

This file introduces only representation data.  It adds no singularity,
degree, or endpoint hypothesis: all coordinates and coefficients are derived
from the live planar-contact family.
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

/-- Source-facing affine data of an arbitrary nonzero exact planar-contact
parameter layer. -/
structure QsOtherFacetPrLeftVParameterAffineLayerData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (order : ℕ) where
  layer_ne : familyParameterLayer D.family order ≠ 0
  k : ℕ
  j : ℕ
  k_pos : 1 ≤ k
  k_le_highest : k ≤ F.highest.n
  j_le_locked : j ≤ F.locked.ell
  coordinates :
    ∀ e ∈ (familyParameterLayer D.family order).support,
      e 0 + e 1 = k ∧
      e 0 + e 2 = j + 1 ∧
      F.V * e 0 + e 3 = F.V * (k + j)
  coefficient_eq_carrier :
    ∀ e ∈ (familyParameterLayer D.family order).support,
      MvPolynomial.coeff e (familyParameterLayer D.family order) =
        MvPolynomial.coeff e P.carrier

namespace QsOtherFacetPrLeftVParameterAffineLayerData

/-- Every nonzero exact planar-contact layer canonically supplies the generic
affine-layer package. -/
theorem exists_of_layer_ne
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {order : ℕ}
    (hLayer : familyParameterLayer D.family order ≠ 0) :
    Nonempty (QsOtherFacetPrLeftVParameterAffineLayerData D order) := by
  rcases D.exists_parameterLayer_affineCoordinates
      hthree houtThree hLayer with
    ⟨k, j, hkpos, hkle, hjle, hall⟩
  exact ⟨{
    layer_ne := hLayer
    k := k
    j := j
    k_pos := hkpos
    k_le_highest := hkle
    j_le_locked := hjle
    coordinates := by
      intro e he
      exact ⟨(hall e he).1, (hall e he).2.1, (hall e he).2.2.1⟩
    coefficient_eq_carrier := by
      intro e he
      exact (hall e he).2.2.2
  }⟩

/-- Coordinate `0` is injective on the support of every exact affine layer. -/
theorem eq_of_zeroCoordinate_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family order).support)
    (hf : f ∈ (familyParameterLayer D.family order).support)
    (hzero : e 0 = f 0) : e = f := by
  rcases A.coordinates e he with ⟨he1, he2, he3⟩
  rcases A.coordinates f hf with ⟨hf1, hf2, hf3⟩
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact hzero
  · have hsum : e 0 + e 1 = e 0 + f 1 := by
      calc
        e 0 + e 1 = A.k := he1
        _ = f 0 + f 1 := hf1.symm
        _ = e 0 + f 1 := by rw [← hzero]
    exact Nat.add_left_cancel hsum
  · have hsum : e 0 + e 2 = e 0 + f 2 := by
      calc
        e 0 + e 2 = A.j + 1 := he2
        _ = f 0 + f 2 := hf2.symm
        _ = e 0 + f 2 := by rw [← hzero]
    exact Nat.add_left_cancel hsum
  · have hsum : F.V * e 0 + e 3 = F.V * e 0 + f 3 := by
      calc
        F.V * e 0 + e 3 = F.V * (A.k + A.j) := he3
        _ = F.V * f 0 + f 3 := hf3.symm
        _ = F.V * e 0 + f 3 := by rw [← hzero]
    exact Nat.add_left_cancel hsum

/-- Honest one-variable coefficient profile of an arbitrary exact affine
layer, indexed by the omitted coordinate `0`. -/
noncomputable def coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (_A : QsOtherFacetPrLeftVParameterAffineLayerData D order) : Polynomial K :=
  ∑ e ∈ (familyParameterLayer D.family order).support,
    Polynomial.monomial (e 0)
      (MvPolynomial.coeff e (familyParameterLayer D.family order))

/-- Injectivity of coordinate `0` means profile coefficients retain the exact
multivariate layer coefficients. -/
theorem coeff_coefficientProfile_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family order).support) :
    A.coefficientProfile.coeff (e 0) =
      MvPolynomial.coeff e (familyParameterLayer D.family order) := by
  classical
  let L := familyParameterLayer D.family order
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
      exact A.eq_of_zeroCoordinate_eq hf (by simpa [L] using he) hcoord
    simp [Polynomial.coeff_monomial, hz]
  · intro hnot
    exact (hnot (by simpa [L] using he)).elim

/-- A nonzero exact parameter layer has a nonzero extracted coefficient
profile. -/
theorem coefficientProfile_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order) :
    A.coefficientProfile ≠ 0 := by
  let L := familyParameterLayer D.family order
  rcases MvPolynomial.support_nonempty.mpr (by simpa [L] using A.layer_ne) with
    ⟨e, he⟩
  have hc : MvPolynomial.coeff e L ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  intro hz
  have hpz : A.coefficientProfile.coeff (e 0) = 0 := by
    simpa using congrArg (fun p : Polynomial K => p.coeff (e 0)) hz
  have hp := A.coeff_coefficientProfile_of_mem
    (e := e) (by simpa [L] using he)
  rw [hp] at hpz
  exact hc (by simpa [L] using hpz)

end QsOtherFacetPrLeftVParameterAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
