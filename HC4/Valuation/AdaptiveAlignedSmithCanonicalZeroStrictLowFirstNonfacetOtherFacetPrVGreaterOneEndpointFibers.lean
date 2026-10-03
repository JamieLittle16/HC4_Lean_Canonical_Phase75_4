import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# A19 exact endpoint fibres of the non-unit PR staircase

The downstream no-interior proof already used the fact that pair degree one is
exactly the locked source pair and pair degree `n` is exactly the certified
primitive-highest pair.  This file extracts those facts as reusable lemmas for
the one-fibre pair-Rees reconstruction.
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

/-- Pair degree one is literally the locked facet/outside source fibre. -/
theorem QsOtherFacetPrLeftVContactFrontierData.eq_locked_of_support_pair_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hpair : (rankThreeQuotientCoordinate 1 F.V e).pair = 1) :
    e = C.ray.facetExponent ∨ e = C.ray.outsideExponent := by
  have hpairNat : e 0 + e 1 = 1 := by
    simpa [rankThreeQuotientCoordinate] using hpair
  have hpairE : qsOtherFacetPairDegree .pr e = (1 : ℤ) := by
    have hcast := congrArg (fun m : ℕ => (m : ℤ)) hpairNat
    simpa [qsOtherFacetPairDegree] using hcast
  have hpairF :
      qsOtherFacetPairDegree .pr C.ray.facetExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.facet_zero, F.locked.facet_one]
  have hqEF :
      rankThreeQuotientCoordinate 1 F.V e =
        rankThreeQuotientCoordinate 1 F.V C.ray.facetExponent :=
    F.quotient.pair_fiber he F.locked.facet_provenance.carrier_mem
      (hpairE.trans hpairF.symm)
  have hpairO :
      qsOtherFacetPairDegree .pr C.ray.outsideExponent = (1 : ℤ) := by
    simp [qsOtherFacetPairDegree,
      F.locked.outside_zero, F.locked.outside_one]
  have hqFO :
      rankThreeQuotientCoordinate 1 F.V C.ray.facetExponent =
        rankThreeQuotientCoordinate 1 F.V C.ray.outsideExponent :=
    F.quotient.pair_fiber
      F.locked.facet_provenance.carrier_mem
      F.locked.outside_provenance.carrier_mem
      (hpairF.trans hpairO.symm)
  have he0cases : e 0 = 0 ∨ e 0 = 1 := by omega
  rcases he0cases with he0 | he0
  · left
    exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
      1 F.V e C.ray.facetExponent hqEF (by
        rw [he0, F.locked.facet_zero])
  · right
    exact eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
      1 F.V e C.ray.outsideExponent (hqEF.trans hqFO) (by
        rw [he0, F.locked.outside_zero])

/-- Pair degree `n` is literally one of the two certified primitive-highest
slice exponents. -/
theorem QsOtherFacetPrLeftVContactFrontierData.eq_highest_of_support_pair_eq_n
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hpair : (rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n) :
    e = F.highest.e0 ∨ e = F.highest.e1 := by
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hlevel : S.pairLevel = (F.highest.n : ℤ) := by
    have hp := (S.support_parent_and_pairLevel he0S).2
    calc
      S.pairLevel = qsOtherFacetPairDegree .pr F.highest.e0 := hp.symm
      _ = (F.highest.n : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.highest.e0_zero, F.highest.e0_one]
  have hpairNat : e 0 + e 1 = F.highest.n := by
    simpa [rankThreeQuotientCoordinate] using hpair
  have hpairE : qsOtherFacetPairDegree .pr e = (F.highest.n : ℤ) := by
    have hcast := congrArg (fun m : ℕ => (m : ℤ)) hpairNat
    simpa [qsOtherFacetPairDegree] using hcast
  have hweight :
      Finsupp.weight (qsOtherFacetPairWeight .pr) e = S.pairLevel := by
    rw [finsupp_weight_qsOtherFacetPairWeight, hpairE, hlevel]
  have hcoeffS : MvPolynomial.coeff e S.slice ≠ 0 := by
    rw [S.slice_eq_initialForm, HC4.Polynomial.coeff_initialForm,
      if_pos hweight]
    exact MvPolynomial.mem_support_iff.mp he
  have heS : e ∈ S.slice.support :=
    MvPolynomial.mem_support_iff.mpr hcoeffS
  rw [F.highest.slice_support_eq] at heS
  simpa only [Finset.mem_insert, Finset.mem_singleton] using heS

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
