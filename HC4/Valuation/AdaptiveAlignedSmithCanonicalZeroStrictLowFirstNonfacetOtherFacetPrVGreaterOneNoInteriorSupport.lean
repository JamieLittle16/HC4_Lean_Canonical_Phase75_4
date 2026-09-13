import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseContactOrder
import Mathlib.Tactic

/-!
# A19 non-unit PR support after strict-interior elimination

The preceding staircase classification leaves one precise local alternative:
a support point may lie strictly between the locked quotient fibre and the
primitive highest quotient fibre.  This file deliberately does **not** assume
how that alternative is eliminated.  Instead it isolates the exact downstream
bookkeeping so the geometric elimination theorem has a one-line consumer.

For the left `(1,V)` orientation, once strict interior support is absent, every
carrier monomial has pair degree either `1` or `n`.  The pair-degree-one fibre
is exactly the locked source pair because its longitudinal coordinate is
bounded by one.  The pair-degree-`n` fibre is exactly the already-certified
highest slice.  Hence the whole carrier support consists of the four literal
source exponents already carrying nonzero coefficient provenance.

No coprimality hypothesis is introduced here.  In particular this file does
not use the conditional primitive-wall arithmetic shortcut.
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

/-- The single geometric obligation left by the whole-carrier staircase
classification in the left non-unit orientation. -/
def QsOtherFacetPrLeftVContactFrontierData.NoStrictInteriorSupport
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) : Prop :=
  ∀ {e : Fin 4 →₀ ℕ}, e ∈ P.carrier.support →
    (rankThreeQuotientCoordinate 1 F.V e).pair = 1 ∨
      (rankThreeQuotientCoordinate 1 F.V e).pair = F.highest.n

/-- Once strict-interior quotient support is absent, the actual planar carrier
has exactly the locked source pair and the primitive highest source pair.
This is a literal support equality, not merely an abstract four-point witness. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_eq_locked_highest_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) :
    P.carrier.support =
      {C.ray.facetExponent, C.ray.outsideExponent,
        F.highest.e0, F.highest.e1} := by
  classical
  have hhighest0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hlevel : S.pairLevel = (F.highest.n : ℤ) := by
    have hp := (S.support_parent_and_pairLevel hhighest0S).2
    calc
      S.pairLevel = qsOtherFacetPairDegree .pr F.highest.e0 := hp.symm
      _ = (F.highest.n : ℤ) := by
        simp [qsOtherFacetPairDegree,
          F.highest.e0_zero, F.highest.e0_one]
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    rcases hno he with hlocked | hhighest
    · have hpairNat : e 0 + e 1 = 1 := by
        simpa [rankThreeQuotientCoordinate] using hlocked
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
      · have heq : e = C.ray.facetExponent :=
          eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 F.V e C.ray.facetExponent hqEF (by
              rw [he0, F.locked.facet_zero])
        exact Or.inl heq
      · have heq : e = C.ray.outsideExponent :=
          eq_of_rankThreeQuotientCoordinate_eq_of_zeroCoordinate_eq
            1 F.V e C.ray.outsideExponent (hqEF.trans hqFO) (by
              rw [he0, F.locked.outside_zero])
        exact Or.inr (Or.inl heq)
    · have hpairNat : e 0 + e 1 = F.highest.n := by
        simpa [rankThreeQuotientCoordinate] using hhighest
      have hpairE :
          qsOtherFacetPairDegree .pr e = (F.highest.n : ℤ) := by
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
      simp only [Finset.mem_insert, Finset.mem_singleton] at heS
      rcases heS with heq | heq
      · exact Or.inr (Or.inr (Or.inl heq))
      · exact Or.inr (Or.inr (Or.inr heq))
  · intro he
    rcases he with he | he | he | he
    · simpa [he] using F.locked.facet_provenance.carrier_mem
    · simpa [he] using F.locked.outside_provenance.carrier_mem
    · simpa [he] using F.highest.e0_provenance.carrier_mem
    · simpa [he] using F.highest.e1_provenance.carrier_mem

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
