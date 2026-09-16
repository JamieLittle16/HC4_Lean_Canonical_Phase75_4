import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairReesFirstInterior
import Mathlib.Tactic

/-!
# A19 affine package for the first positive unit pair-Rees layer

The unit pair-degree reverse Rees already produces a genuine first positive
strict-interior layer.  This file keeps that layer source-honest: all supported
monomials lie in one exact unit quotient fibre, have literal unchanged carrier
coefficients, and therefore admit the same affine-fibre interface used by the
non-unit finite-staircase chain.

No new Rees family or determinant argument is introduced here.
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

/-- Exact source-facing data of the first positive pair-Rees layer in the left
unit `(1,1)` orientation. -/
structure QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n) where
  k : ℕ
  j : ℕ
  k_gt_one : 1 < k
  k_lt_highest : k < F.highest.n
  j_pos : 0 < j
  j_lt_locked : j < F.locked.ell
  coordinates :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support,
      e 0 + e 1 = k ∧
      e 0 + e 2 = j + 1 ∧
      e 0 + e 3 = k + j
  coefficient_eq_carrier :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support,
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer)) =
        MvPolynomial.coeff e P.carrier

namespace QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

/-- Two monomials in the selected unit layer have the same exact quotient
coordinates. -/
private theorem firstPositiveLayer_coordinates_relative
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support)
    {j : ℕ}
    (hj :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e).firstTransverse =
        j + 1) :
    f 0 + f 1 = e 0 + e 1 ∧
      f 0 + f 2 = j + 1 ∧
      f 0 + f 3 = (e 0 + e 1) + j := by
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    have hs := D.parameterLayer_support q
    rw [hs] at he
    exact Finset.mem_filter.mp he
  have hfFilter :
      f ∈ P.carrier.support ∧ F.highest.n - (f 0 + f 1) = q := by
    have hs := D.parameterLayer_support q
    rw [hs] at hf
    exact Finset.mem_filter.mp hf
  rcases F.support_staircase_classification hthree houtThree heFilter.1 with
    ⟨_je, _hje, heN, _hjelle, _hjzeroe, _hjlockede⟩
  rcases F.support_staircase_classification hthree houtThree hfFilter.1 with
    ⟨_jf, _hjf, hfN, _hjellf, _hjzerof, _hjlockedf⟩
  have hpairNat : f 0 + f 1 = e 0 + e 1 := by
    have heN' : e 0 + e 1 ≤ F.highest.n := by
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using heN
    have hfN' : f 0 + f 1 ≤ F.highest.n := by
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hfN
    omega
  have hpairZ :
      qsOtherFacetPairDegree .pr f = qsOtherFacetPairDegree .pr e := by
    simp only [qsOtherFacetPairDegree]
    exact_mod_cast hpairNat
  have hfiber := F.quotient.pair_fiber hfFilter.1 heFilter.1 hpairZ
  have hfirstQ := congrArg
    HC4.Polynomial.RankThreeQuotientCoordinate.firstTransverse hfiber
  have hfirst : f 0 + f 2 = j + 1 := by
    have hq :
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 1 f).firstTransverse =
          j + 1 := hfirstQ.trans hj
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hq
  have hstair := F.support_staircase_equations hthree houtThree hfFilter.1
  have hsecondZ := hstair.2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hsecondZ
  rw [hpairNat, hfirst] at hsecondZ
  have hsecond : f 0 + f 3 = (e 0 + e 1) + j := by
    have hsecondZ' :
        ((f 0 + f 3 : ℕ) : ℤ) = (((e 0 + e 1) + j : ℕ) : ℤ) := by
      push_cast at hsecondZ ⊢
      nlinarith
    exact_mod_cast hsecondZ'
  exact ⟨hpairNat, hfirst, hsecond⟩

/-- Failure of endpoint-only support canonically produces the affine package
for the first positive unit pair-Rees layer. -/
theorem exists_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D) := by
  classical
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hLne : familyParameterLayer D.family q ≠ 0 := by
    dsimp [q]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  have heInterior :=
    D.firstPositiveLayer_pair_strictInterior_unitLeft F hthree houtThree hnot e he
  have hsupport := D.parameterLayer_support q
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    rw [hsupport] at he
    exact Finset.mem_filter.mp he
  let k := e 0 + e 1
  rcases F.support_staircase_classification hthree houtThree heFilter.1 with
    ⟨j, hj, _hkN, hjell, hjzero, hjlocked⟩
  have hkgt : 1 < k := by simpa [k] using heInterior.1
  have hklt : k < F.highest.n := by simpa [k] using heInterior.2
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos h
    have hkEq := hjzero.mp hj0
    have : k = F.highest.n := by
      simpa [k, HC4.Polynomial.rankThreeQuotientCoordinate] using hkEq
    omega
  have hjlt : j < F.locked.ell := by
    by_contra h
    have hjeq : j = F.locked.ell := by omega
    have hkEq := hjlocked.mp hjeq
    have : k = 1 := by
      simpa [k, HC4.Polynomial.rankThreeQuotientCoordinate] using hkEq
    omega
  exact ⟨{
    k := k
    j := j
    k_gt_one := hkgt
    k_lt_highest := hklt
    j_pos := hjpos
    j_lt_locked := hjlt
    coordinates := by
      intro f hf
      have hcoords := firstPositiveLayer_coordinates_relative
        F D hthree houtThree he hf hj
      simpa [k] using hcoords
    coefficient_eq_carrier := by
      intro f hf
      have hfFilter :
          f ∈ P.carrier.support ∧ F.highest.n - (f 0 + f 1) = q := by
        have hs := D.parameterLayer_support q
        rw [hs] at hf
        exact Finset.mem_filter.mp hf
      rw [D.parameterLayer_coeff]
      have hq :
          F.highest.n - (f 0 + f 1) =
            firstPositiveActualParameterOrder D.family D.positiveLayer := by
        simpa [q] using hfFilter.2
      simp [hfFilter.1, hq]
  }⟩

end QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
