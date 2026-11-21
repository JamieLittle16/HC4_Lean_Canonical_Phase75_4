import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPlanarContactFirstInterior
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairReesFirstInterior
import Mathlib.Tactic

/-!
# A19 unit extremal surviving fibres of the finite staircase

The two honest unit Rees families select opposite ends of the same finite
strict-interior staircase.  The locked/contact reverse Rees selects the least
surviving interior pair degree, while the pair-degree reverse Rees selects the
greatest one.

This is source/order bookkeeping only.  No determinant identity is introduced.
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

namespace QsOtherFacetPrUnitLeftPlanarContactReesData

/-- The first positive unit contact layer has minimal pair degree among all
surviving strict-interior carrier fibres. -/
theorem firstPositiveLayer_pair_minimal
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}
    (D : QsOtherFacetPrUnitLeftPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {a e : Fin 4 →₀ ℕ}
    (ha : a ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support)
    (he : e ∈ P.carrier.support)
    (hegt : 1 < (rankThreeQuotientCoordinate 1 1 e).pair)
    (_helt : (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n) :
    (rankThreeQuotientCoordinate 1 1 a).pair ≤
      (rankThreeQuotientCoordinate 1 1 e).pair := by
  let q := T.topFace.degree - Finsupp.weight (qsIntegralContactWeight 2) e
  have heLayer : e ∈ (familyParameterLayer D.family q).support := by
    simpa [q] using D.parameterLayer_mem_of_carrier_mem he
  have hcoeff : (MvPolynomial.coeff e D.family).coeff q ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp heLayer
    rw [familyParameterLayer_coeff] at h
    exact h
  have heFamily : e ∈ D.family.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hqmem : q ∈ familyParameterLayerOrders D.family :=
    (mem_familyParameterLayerOrders_iff D.family q).2
      ⟨e, heFamily, hcoeff⟩
  have hqpos : 0 < q := by
    dsimp [q]
    exact D.reverseOrder_pos_of_strictInterior hthree houtThree he hegt
  have hfirstle :
      firstPositiveActualParameterOrder D.family D.hasPositiveLayer ≤ q :=
    firstPositiveActualParameterOrder_le
      D.family D.hasPositiveLayer hqmem hqpos

  rcases D.parameterLayer_support_source_and_order ha with ⟨haP, haOrder⟩
  have haInterior :=
    D.firstPositiveLayer_pair_strictInterior_of_not_noStrictInterior
      hthree houtThree hnot ha
  have hA := F.contactOrder_interpolation hthree houtThree haP
  rw [← D.reverseOrder_eq_quotientContactOrder a, haOrder] at hA
  have hE := F.contactOrder_interpolation hthree houtThree he
  rw [← D.reverseOrder_eq_quotientContactOrder e] at hE
  change
    (F.highest.n - 1) * q =
      2 * (F.locked.ell + 1 - F.highest.n) *
        ((rankThreeQuotientCoordinate 1 1 e).pair - 1) at hE

  let B := 2 * (F.locked.ell + 1 - F.highest.n)
  have hgap : 0 < F.locked.ell + 1 - F.highest.n :=
    Nat.sub_pos_of_lt (F.highest_n_lt_locked_height hthree houtThree)
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) hgap
  have hscaled :
      (F.highest.n - 1) *
          firstPositiveActualParameterOrder D.family D.hasPositiveLayer ≤
        (F.highest.n - 1) * q :=
    Nat.mul_le_mul_left (F.highest.n - 1) hfirstle
  have hpairs :
      B * ((rankThreeQuotientCoordinate 1 1 a).pair - 1) ≤
        B * ((rankThreeQuotientCoordinate 1 1 e).pair - 1) := by
    calc
      B * ((rankThreeQuotientCoordinate 1 1 a).pair - 1) =
          (F.highest.n - 1) *
            firstPositiveActualParameterOrder D.family D.hasPositiveLayer := by
              simpa [B] using hA.symm
      _ ≤ (F.highest.n - 1) * q := hscaled
      _ = B * ((rankThreeQuotientCoordinate 1 1 e).pair - 1) := by
        simpa [B] using hE
  have hsub :
      (rankThreeQuotientCoordinate 1 1 a).pair - 1 ≤
        (rankThreeQuotientCoordinate 1 1 e).pair - 1 := by
    by_contra hnotle
    have hlt :
        (rankThreeQuotientCoordinate 1 1 e).pair - 1 <
          (rankThreeQuotientCoordinate 1 1 a).pair - 1 :=
      Nat.lt_of_not_ge hnotle
    have hmul := Nat.mul_lt_mul_of_pos_left hlt hB
    exact (not_lt_of_ge hpairs) hmul
  omega

end QsOtherFacetPrUnitLeftPlanarContactReesData

namespace QsOtherFacetPrPairReesData

/-- The first positive pair-Rees layer has maximal pair degree among all
surviving strict-interior unit carrier fibres. -/
theorem firstPositiveLayer_pair_maximal_unitLeft
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    {a e : Fin 4 →₀ ℕ}
    (ha : a ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support)
    (he : e ∈ P.carrier.support)
    (_hegt : 1 < (rankThreeQuotientCoordinate 1 1 e).pair)
    (helt : (rankThreeQuotientCoordinate 1 1 e).pair < F.highest.n) :
    (rankThreeQuotientCoordinate 1 1 e).pair ≤
      (rankThreeQuotientCoordinate 1 1 a).pair := by
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have haFilter :
      a ∈ P.carrier.support ∧ F.highest.n - (a 0 + a 1) = q := by
    have hs := D.parameterLayer_support q
    rw [hs] at ha
    exact Finset.mem_filter.mp ha
  have haInterior :=
    D.firstPositiveLayer_pair_strictInterior_unitLeft
      F hthree houtThree hnot a (by simpa [q] using ha)

  have hePairNat : e 0 + e 1 < F.highest.n := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using helt
  let qe := F.highest.n - (e 0 + e 1)
  have hqepos : 0 < qe := by
    dsimp [qe]
    omega
  have heLayer : e ∈ (familyParameterLayer D.family qe).support := by
    rw [D.parameterLayer_support qe]
    exact Finset.mem_filter.mpr ⟨he, rfl⟩
  have hcoeff : (MvPolynomial.coeff e D.family).coeff qe ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp heLayer
    rw [familyParameterLayer_coeff] at h
    exact h
  have heFamily : e ∈ D.family.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hqemem : qe ∈ familyParameterLayerOrders D.family :=
    (mem_familyParameterLayerOrders_iff D.family qe).2
      ⟨e, heFamily, hcoeff⟩
  have hqle : q ≤ qe := by
    dsimp [q]
    exact firstPositiveActualParameterOrder_le
      D.family D.positiveLayer hqemem hqepos

  have haPairNat : 1 < a 0 + a 1 ∧ a 0 + a 1 < F.highest.n :=
    haInterior
  have hpairNat : e 0 + e 1 ≤ a 0 + a 1 := by
    dsimp [q, qe] at hqle
    omega
  simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hpairNat

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
