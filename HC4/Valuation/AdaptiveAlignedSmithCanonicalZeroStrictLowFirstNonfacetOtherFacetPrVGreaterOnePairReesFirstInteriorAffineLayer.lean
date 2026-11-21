import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInterior
import Mathlib.Tactic

/-!
# A19 affine package for the first positive primitive-highest pair-Rees layer

The pair-degree reverse Rees is oriented from the primitive highest slice.
If strict-interior support survives, its first positive actual layer is already
known to have pair degree strictly between `1` and the highest degree `n`.

This file proves that the whole selected layer is one honest staircase fibre.
It therefore has literal source exponents

    (t, k-t, j+1-t, V*(k+j-t))

for fixed strict-interior integers `k,j`, and its coefficients are unchanged
coefficients of the source-honest planar carrier.
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
`(1,V)` orientation. -/
structure QsOtherFacetPrPairFirstInteriorAffineLayerData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
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
      F.V * e 0 + e 3 = F.V * (k + j)
  coefficient_eq_carrier :
    ∀ e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support,
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer)) =
        MvPolynomial.coeff e P.carrier

namespace QsOtherFacetPrPairFirstInteriorAffineLayerData

/-- Two monomials in the first positive pair-Rees layer lie in the same exact
quotient-staircase fibre.  This is split out of the package constructor so the
large support/classification calculation has its own heartbeat budget. -/
private theorem firstPositiveLayer_coordinates_relative
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
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
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).firstTransverse =
        j + 1) :
    f 0 + f 1 = e 0 + e 1 ∧
      f 0 + f 2 = j + 1 ∧
      F.V * f 0 + f 3 = F.V * ((e 0 + e 1) + j) := by
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    have hs :
        (familyParameterLayer D.family q).support =
          P.carrier.support.filter fun a =>
            F.highest.n - (a 0 + a 1) = q :=
      D.parameterLayer_support q
    rw [hs] at he
    exact Finset.mem_filter.mp he
  have hfFilter :
      f ∈ P.carrier.support ∧ F.highest.n - (f 0 + f 1) = q := by
    have hs :
        (familyParameterLayer D.family q).support =
          P.carrier.support.filter fun a =>
            F.highest.n - (a 0 + a 1) = q :=
      D.parameterLayer_support q
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
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).firstTransverse =
          j + 1 := hfirstQ.trans hj
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hq
  have hstair := F.support_staircase_equations hthree houtThree hfFilter.1
  have hsecondZ := hstair.2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hsecondZ
  rw [hpairNat, hfirst] at hsecondZ
  have hsecond :
      F.V * f 0 + f 3 = F.V * ((e 0 + e 1) + j) := by
    have hsecondZ' :
        ((F.V * f 0 + f 3 : ℕ) : ℤ) =
          ((F.V * ((e 0 + e 1) + j) : ℕ) : ℤ) := by
      push_cast at hsecondZ ⊢
      nlinarith
    exact_mod_cast hsecondZ'
  exact ⟨hpairNat, hfirst, hsecond⟩

/-- Failure of endpoint-only support canonically produces the affine package
for the first positive pair-Rees layer. -/
theorem exists_of_not_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrPairFirstInteriorAffineLayerData F D) := by
  classical
  let q := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hLne : familyParameterLayer D.family q ≠ 0 := by
    dsimp [q]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hLne with ⟨e, he⟩
  have heInterior :=
    D.firstPositiveLayer_pair_strictInterior_left F hthree houtThree hnot e he
  have hsupport :
      (familyParameterLayer D.family q).support =
        P.carrier.support.filter fun a =>
          F.highest.n - (a 0 + a 1) = q :=
    D.parameterLayer_support q
  have heFilter :
      e ∈ P.carrier.support ∧ F.highest.n - (e 0 + e 1) = q := by
    rw [hsupport] at he
    exact Finset.mem_filter.mp he
  let k := e 0 + e 1
  rcases F.support_staircase_classification hthree houtThree heFilter.1 with
    ⟨j, hj, hkN, hjell, hjzero, hjlocked⟩
  have hkgt : 1 < k := by simpa [k] using heInterior.1
  have hklt : k < F.highest.n := by simpa [k] using heInterior.2
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos h
    have hkEq :
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair =
          F.highest.n := (hjzero.mp hj0)
    have : k = F.highest.n := by
      simpa [k, HC4.Polynomial.rankThreeQuotientCoordinate] using hkEq
    omega
  have hjlt : j < F.locked.ell := by
    have hjle : j ≤ F.locked.ell := hjell
    by_contra h
    have hjeq : j = F.locked.ell := by omega
    have hkEq :
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair = 1 :=
      hjlocked.mp hjeq
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
        have hs :
            (familyParameterLayer D.family q).support =
              P.carrier.support.filter fun a =>
                F.highest.n - (a 0 + a 1) = q :=
          D.parameterLayer_support q
        rw [hs] at hf
        exact Finset.mem_filter.mp hf
      rw [D.parameterLayer_coeff]
      have hq :
          F.highest.n - (f 0 + f 1) =
            firstPositiveActualParameterOrder D.family D.positiveLayer := by
        simpa [q] using hfFilter.2
      simp [hfFilter.1, hq]
  }⟩

/-- Coordinate `0` is injective on the selected pair-Rees layer. -/
theorem eq_of_zeroCoordinate_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support)
    (hf : f ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support)
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
        _ = e 0 + f 1 := by rw [hzero]
    exact Nat.add_left_cancel hsum
  · have hsum : e 0 + e 2 = e 0 + f 2 := by
      calc
        e 0 + e 2 = A.j + 1 := he2
        _ = f 0 + f 2 := hf2.symm
        _ = e 0 + f 2 := by rw [hzero]
    exact Nat.add_left_cancel hsum
  · have hsum : F.V * e 0 + e 3 = F.V * e 0 + f 3 := by
      calc
        F.V * e 0 + e 3 = F.V * (A.k + A.j) := he3
        _ = F.V * f 0 + f 3 := hf3.symm
        _ = F.V * e 0 + f 3 := by rw [hzero]
    exact Nat.add_left_cancel hsum

/-- Honest one-variable coefficient profile of the selected pair-Rees layer. -/
noncomputable def coefficientProfile
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (_A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) : Polynomial K :=
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
  ∑ e ∈ L.support, Polynomial.monomial (e 0) (MvPolynomial.coeff e L)

/-- The profile retains each selected layer coefficient literally. -/
theorem coeff_coefficientProfile_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ (familyParameterLayer D.family
      (firstPositiveActualParameterOrder D.family D.positiveLayer)).support) :
    A.coefficientProfile.coeff (e 0) =
      MvPolynomial.coeff e (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.positiveLayer)) := by
  classical
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
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

/-- The extracted first pair-Rees profile is nonzero. -/
theorem coefficientProfile_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrPairReesData C P S F.highest.n}
    (A : QsOtherFacetPrPairFirstInteriorAffineLayerData F D) :
    A.coefficientProfile ≠ 0 := by
  let L := familyParameterLayer D.family
    (firstPositiveActualParameterOrder D.family D.positiveLayer)
  have hL : L ≠ 0 := by
    dsimp [L]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hL with ⟨e, he⟩
  have hc : MvPolynomial.coeff e L ≠ 0 := MvPolynomial.mem_support_iff.mp he
  intro hz
  have hpz : A.coefficientProfile.coeff (e 0) = 0 := by
    simpa using congrArg (fun p : Polynomial K => p.coeff (e 0)) hz
  have hp := A.coeff_coefficientProfile_of_mem (e := e) (by simpa [L] using he)
  rw [hp] at hpz
  exact hc (by simpa [L] using hpz)

end QsOtherFacetPrPairFirstInteriorAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
