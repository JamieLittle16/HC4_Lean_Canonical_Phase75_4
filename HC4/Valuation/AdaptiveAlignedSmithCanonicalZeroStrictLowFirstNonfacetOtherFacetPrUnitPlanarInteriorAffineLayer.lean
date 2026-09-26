import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarContactFirstInterior
import Mathlib.Tactic

/-!
# A19 affine package for the locked-side first unit interior layer

The least positive unit contact layer occupies one exact strict-interior
quotient fibre.  Expanding the unit staircase equation gives literal source
coordinates `(t,k-t,j+1-t,k+j-t)`.  Coordinate zero is therefore injective on
support and yields the honest one-variable coefficient profile used by the
endpoint variation machinery.
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

structure QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F) where
  k : ℕ
  j : ℕ
  k_gt_one : 1 < k
  k_lt_highest : k < F.highest.n
  j_pos : 0 < j
  j_lt_locked : j < F.locked.ell
  coordinates :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
      e 0 + e 1 = k ∧ e 0 + e 2 = j + 1 ∧ e 0 + e 3 = k + j
  coefficient_eq_carrier :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) =
        MvPolynomial.coeff e P.carrier

namespace QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

/-- The live strict-interior unit branch canonically produces the locked-side
affine package. -/
theorem exists_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) := by
  rcases D.exists_firstPositiveLayer_strictInterior_fiber hthree houtThree hnot with
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
      rcases hall e he with ⟨hpair, hfirst, _hcoeff⟩
      have hpairNat : e 0 + e 1 = k := by
        simpa [QsOtherFacetPrUnitLeftPlanarContactReesData.rankThreeQuotientCoordinate,
          HC4.Polynomial.rankThreeQuotientCoordinate] using hpair
      have hfirstNat : e 0 + e 2 = j + 1 := by
        simpa [QsOtherFacetPrUnitLeftPlanarContactReesData.rankThreeQuotientCoordinate,
          HC4.Polynomial.rankThreeQuotientCoordinate] using hfirst
      have heP := (D.parameterLayer_support_source_and_order he).1
      have hs := F.support_staircase_equations hthree houtThree heP
      have hsecondZ := hs.2
      simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
        HC4.Polynomial.rankThreeQuotientCoordinate_pair,
        HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse, one_mul] at hsecondZ
      rw [hpairNat, hfirstNat] at hsecondZ
      have hsecondZ' : ((e 0 + e 3 : ℕ) : ℤ) = ((k + j : ℕ) : ℤ) := by
        push_cast at hsecondZ ⊢
        nlinarith
      exact ⟨hpairNat, hfirstNat, by exact_mod_cast hsecondZ'⟩
    coefficient_eq_carrier := by
      intro e he
      exact D.parameterLayer_coeff_eq_carrier_of_mem he
  }⟩

/-- Coordinate zero is injective on the selected locked-side unit layer. -/
theorem eq_of_zeroCoordinate_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (hzero : e 0 = f 0) : e = f := by
  rcases A.coordinates e he with ⟨he1, he2, he3⟩
  rcases A.coordinates f hf with ⟨hf1, hf2, hf3⟩
  have h1sum : e 0 + e 1 = f 0 + f 1 := he1.trans hf1.symm
  have h2sum : e 0 + e 2 = f 0 + f 2 := he2.trans hf2.symm
  have h3sum : e 0 + e 3 = f 0 + f 3 := he3.trans hf3.symm
  have h1 : e 1 = f 1 := by
    rw [hzero] at h1sum
    exact Nat.add_left_cancel h1sum
  have h2 : e 2 = f 2 := by
    rw [hzero] at h2sum
    exact Nat.add_left_cancel h2sum
  have h3 : e 3 = f 3 := by
    rw [hzero] at h3sum
    exact Nat.add_left_cancel h3sum
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact hzero
  · exact h1
  · exact h2
  · exact h3

noncomputable def coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (_A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) : Polynomial K :=
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  ∑ e ∈ L.support, Polynomial.monomial (e 0) (MvPolynomial.coeff e L)

theorem coeff_coefficientProfile_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support) :
    A.coefficientProfile.coeff (e 0) =
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) := by
  classical
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)
  change (∑ f ∈ L.support,
    Polynomial.monomial (f 0) (MvPolynomial.coeff f L)).coeff (e 0) =
      MvPolynomial.coeff e L
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hz : f 0 ≠ e 0 := by
      intro hcoord
      apply hfe
      exact A.eq_of_zeroCoordinate_eq hf he hcoord
    simp [Polynomial.coeff_monomial, hz]
  · intro hnot
    exact (hnot he).elim

theorem coefficientProfile_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    {D : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (A : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData D) :
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

end QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
