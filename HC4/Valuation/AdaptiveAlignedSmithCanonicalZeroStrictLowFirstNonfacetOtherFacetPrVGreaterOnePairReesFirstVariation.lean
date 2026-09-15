import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesHighestMomentRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePairReesFirstInterior
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerMomentRealisation
import HC4.Valuation.PlanarHighestFirstVariationBridge
import Mathlib.Tactic

/-!
# A19 first pair-Rees layer -> highest-end affine two-root equation

The pair-degree reverse Rees starts at the primitive highest binomial.  Under
failure of `NoStrictInteriorSupport`, its least positive actual layer is the
highest surviving strict-interior pair fibre.

Rather than duplicate the existing affine-profile machinery, this file shows
that this exact pair-Rees layer is literally the corresponding exact layer of
the source-honest planar-contact Rees.  Pair degree determines contact order
injectively by the retained interpolation law.  We may therefore reuse the
arbitrary-contact-layer affine profile and moment realisation unchanged.

The generic highest-end dual-jet bridge then yields the affine two-root Euler
equation with roots `j,j+1` for the highest surviving interior profile.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

/-- The first positive pair-Rees layer is exactly one existing contact-Rees
layer.  The returned contact affine package is therefore also a source-honest
profile package for the pair-Rees first layer. -/
theorem exists_firstPositiveLayer_contactAffineData_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (E : QsOtherFacetPrLeftVPlanarContactReesData F)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ (contactOrder : ℕ)
        (A : QsOtherFacetPrLeftVParameterAffineLayerData E contactOrder),
      familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.positiveLayer) =
        familyParameterLayer E.family contactOrder ∧
      1 < A.k ∧ A.k < F.highest.n ∧
      0 < A.j ∧ A.j < F.locked.ell := by
  classical
  let qPair := firstPositiveActualParameterOrder D.family D.positiveLayer
  have hPairLayer : familyParameterLayer D.family qPair ≠ 0 := by
    dsimp [qPair]
    exact firstPositiveActualParameterLayer_ne_zero D.family D.positiveLayer
  rcases MvPolynomial.support_nonempty.mpr hPairLayer with ⟨e, hePair⟩
  have heFilter :
      e ∈ P.carrier.support ∧
        F.highest.n - (e 0 + e 1) = qPair := by
    have hs := D.parameterLayer_support qPair
    rw [hs] at hePair
    exact Finset.mem_filter.mp hePair
  have heP : e ∈ P.carrier.support := heFilter.1
  have heStrict := D.firstPositiveLayer_pair_strictInterior_left
    F hthree houtThree hnot e hePair

  let qContact := T.topFace.degree -
    Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e
  have heContact :
      e ∈ (familyParameterLayer E.family qContact).support := by
    dsimp [qContact]
    exact E.parameterLayer_mem_of_carrier_mem heP
  have hContactLayer : familyParameterLayer E.family qContact ≠ 0 :=
    MvPolynomial.support_nonempty.mpr ⟨e, heContact⟩

  have samePair_of_pairLayer
      {f : Fin 4 →₀ ℕ}
      (hf : f ∈ (familyParameterLayer D.family qPair).support) :
      f 0 + f 1 = e 0 + e 1 := by
    have hfs := D.parameterLayer_support qPair
    have hes := D.parameterLayer_support qPair
    rw [hfs] at hf
    have hfFilter := Finset.mem_filter.mp hf
    have hfP : f ∈ P.carrier.support := hfFilter.1
    have hfLe : f 0 + f 1 ≤ F.highest.n := by
      rcases F.support_staircase_classification hthree houtThree hfP with
        ⟨j, _hj, hk, _hjle, _hzero, _hlocked⟩
      simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hk
    have heLe : e 0 + e 1 ≤ F.highest.n := by omega
    omega

  have sameContactOrder_of_samePair
      {f : Fin 4 →₀ ℕ} (hfP : f ∈ P.carrier.support)
      (hpair : f 0 + f 1 = e 0 + e 1) :
      T.topFace.degree -
          Finsupp.weight (qsIntegralContactWeight (F.V + 1)) f =
        qContact := by
    have hfInterp := F.contactOrder_interpolation hthree houtThree hfP
    have heInterp := F.contactOrder_interpolation hthree houtThree heP
    rw [← E.reverseOrder_eq_quotientContactOrder hthree houtThree f] at hfInterp
    rw [← E.reverseOrder_eq_quotientContactOrder hthree houtThree e] at heInterp
    have hnpos : 0 < F.highest.n - 1 := by omega
    have hpairQ :
        (rankThreeQuotientCoordinate 1 F.V f).pair =
          (rankThreeQuotientCoordinate 1 F.V e).pair := by
      simpa [rankThreeQuotientCoordinate] using hpair
    have hmul :
        (F.highest.n - 1) *
            (T.topFace.degree -
              Finsupp.weight (qsIntegralContactWeight (F.V + 1)) f) =
          (F.highest.n - 1) *
            (T.topFace.degree -
              Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e) := by
      calc
        (F.highest.n - 1) *
            (T.topFace.degree -
              Finsupp.weight (qsIntegralContactWeight (F.V + 1)) f) =
          (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
            ((rankThreeQuotientCoordinate 1 F.V f).pair - 1) := hfInterp
        _ = (F.V + 1) * (F.locked.ell + 1 - F.highest.n) *
            ((rankThreeQuotientCoordinate 1 F.V e).pair - 1) := by rw [hpairQ]
        _ = (F.highest.n - 1) *
            (T.topFace.degree -
              Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e) := heInterp.symm
    have horder := Nat.mul_left_cancel hnpos hmul
    simpa [qContact] using horder

  have hPairToContact :
      ∀ {f : Fin 4 →₀ ℕ},
        f ∈ (familyParameterLayer D.family qPair).support →
          f ∈ (familyParameterLayer E.family qContact).support := by
    intro f hfPair
    have hfs := D.parameterLayer_support qPair
    have hfPair' := hfPair
    rw [hfs] at hfPair'
    have hfFilter := Finset.mem_filter.mp hfPair'
    have hfP : f ∈ P.carrier.support := hfFilter.1
    have hpair := samePair_of_pairLayer hfPair
    have horder := sameContactOrder_of_samePair hfP hpair
    have hm := E.parameterLayer_mem_of_carrier_mem hfP
    rw [horder] at hm
    exact hm

  have hContactToPair :
      ∀ {f : Fin 4 →₀ ℕ},
        f ∈ (familyParameterLayer E.family qContact).support →
          f ∈ (familyParameterLayer D.family qPair).support := by
    intro f hfContact
    rcases E.parameterLayer_support_source_and_order hfContact with
      ⟨hfP, hfOrder⟩
    have heOrder :
        T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight (F.V + 1)) e =
          qContact := by rfl
    have hpairQ := E.pair_eq_of_reverseOrder_eq hthree houtThree
      hfP heP (hfOrder.trans heOrder.symm)
    have hpair : f 0 + f 1 = e 0 + e 1 := by
      simpa [rankThreeQuotientCoordinate] using hpairQ
    have hfPairOrder : F.highest.n - (f 0 + f 1) = qPair := by
      rw [hpair]
      exact heFilter.2
    rw [D.parameterLayer_support qPair]
    exact Finset.mem_filter.mpr ⟨hfP, hfPairOrder⟩

  have hsupport :
      (familyParameterLayer D.family qPair).support =
        (familyParameterLayer E.family qContact).support := by
    ext f
    constructor
    · exact hPairToContact
    · exact hContactToPair

  have hlayer :
      familyParameterLayer D.family qPair =
        familyParameterLayer E.family qContact := by
    apply MvPolynomial.ext
    intro f
    by_cases hf : f ∈ (familyParameterLayer D.family qPair).support
    · have hfC : f ∈ (familyParameterLayer E.family qContact).support := by
        rw [← hsupport]
        exact hf
      have hfFilter :
          f ∈ P.carrier.support ∧
            F.highest.n - (f 0 + f 1) = qPair := by
        have hs := D.parameterLayer_support qPair
        rw [hs] at hf
        exact Finset.mem_filter.mp hf
      rw [D.parameterLayer_coeff qPair f, if_pos hfFilter]
      exact (E.parameterLayer_coeff_eq_carrier_of_mem hfC).symm
    · have hfC : f ∉ (familyParameterLayer E.family qContact).support := by
        intro h
        apply hf
        rw [hsupport]
        exact h
      rw [MvPolynomial.notMem_support_iff.mp hf,
        MvPolynomial.notMem_support_iff.mp hfC]

  let A : QsOtherFacetPrLeftVParameterAffineLayerData E qContact :=
    Classical.choice
      (QsOtherFacetPrLeftVParameterAffineLayerData.exists_of_layer_ne
        E hthree houtThree hContactLayer)

  have heCoords := A.coordinates e heContact
  have hkEq : A.k = e 0 + e 1 := heCoords.1.symm
  have hkgt : 1 < A.k := by rw [hkEq]; exact heStrict.1
  have hklt : A.k < F.highest.n := by rw [hkEq]; exact heStrict.2

  rcases F.support_staircase_classification hthree houtThree heP with
    ⟨j0, hj0, _hkle, hj0le, hj0zero, hj0locked⟩
  have hfirstA :
      (rankThreeQuotientCoordinate 1 F.V e).firstTransverse = A.j + 1 := by
    simpa [rankThreeQuotientCoordinate] using heCoords.2.1
  have hjEq : A.j = j0 := by
    have : A.j + 1 = j0 + 1 := by
      calc
        A.j + 1 =
            (rankThreeQuotientCoordinate 1 F.V e).firstTransverse :=
          hfirstA.symm
        _ = j0 + 1 := hj0
    omega
  have hjpos : 0 < A.j := by
    rw [hjEq]
    by_contra h
    have hjz : j0 = 0 := Nat.eq_zero_of_not_pos h
    have hkTop := hj0zero.mp hjz
    have hePair :
        (rankThreeQuotientCoordinate 1 F.V e).pair = e 0 + e 1 := by
      simp [rankThreeQuotientCoordinate]
    rw [hePair] at hkTop
    omega
  have hjlt : A.j < F.locked.ell := by
    rw [hjEq]
    have hjle := hj0le
    by_contra h
    have hjeq : j0 = F.locked.ell := by omega
    have hkOne := hj0locked.mp hjeq
    have hePair :
        (rankThreeQuotientCoordinate 1 F.V e).pair = e 0 + e 1 := by
      simp [rankThreeQuotientCoordinate]
    rw [hePair] at hkOne
    omega

  exact ⟨qContact, A, by simpa [qPair] using hlayer,
    hkgt, hklt, hjpos, hjlt⟩

/-- **Highest-end equation for the highest surviving interior fibre.**
The profile comes from the existing exact contact-layer affine package, while
the singular family is the highest-oriented pair Rees. -/
theorem exists_firstPositiveLayer_highestEulerEquation_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (E : QsOtherFacetPrLeftVPlanarContactReesData F)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ (contactOrder : ℕ)
        (A : QsOtherFacetPrLeftVParameterAffineLayerData E contactOrder),
      1 < A.k ∧ A.k < F.highest.n ∧
      0 < A.j ∧ A.j < F.locked.ell ∧
      HC4.Polynomial.affineTwoRootEulerOperator
        ((MvPolynomial.coeff F.highest.e0 S.slice) * (F.highest.n : K))
        ((MvPolynomial.coeff F.highest.e1 S.slice) *
          ((F.highest.n - 1 : ℕ) : K))
        A.j A.coefficientProfile = 0 := by
  rcases D.exists_firstPositiveLayer_contactAffineData_left
      F E hthree houtThree hnot with
    ⟨contactOrder, A, hlayer, hkgt, hklt, hjgt, hjlt⟩
  let c : K := MvPolynomial.coeff F.highest.e0 S.slice
  let d : K := MvPolynomial.coeff F.highest.e1 S.slice
  have he0S : F.highest.e0 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have he1S : F.highest.e1 ∈ S.slice.support := by
    rw [F.highest.slice_support_eq]
    simp
  have hc : c ≠ 0 := by
    dsimp [c]
    exact MvPolynomial.mem_support_iff.mp he0S
  have hd : d ≠ 0 := by
    dsimp [d]
    exact MvPolynomial.mem_support_iff.mp he1S
  have hzero := D.zeroLayer_specialisedEulerHessian_eq_highestBinomialMomentHessian_left F
  have hcontactMoment := A.specialisedEulerHessian_eq_parallelStaircaseMomentHessian
  have hfirst :
      (fun r s =>
        HC4.Polynomial.rankThreeLineSpecialisation
          (HC4.Polynomial.eulerScaledHessian
            (familyParameterLayer D.family
              (firstPositiveActualParameterOrder D.family D.positiveLayer)) r s)) =
        HC4.Polynomial.parallelStaircaseMomentHessian
          F.V A.k A.j A.coefficientProfile := by
    rw [hlayer]
    exact hcontactMoment
  have hEuler :=
    affineTwoRootEulerOperator_eq_zero_of_firstActual_highest_moment_identification
      D.family D.positiveLayer D.hessian_zero
      F.V F.highest.n A.k A.j
      (by omega : 0 < F.V) F.highest.n_two_le
      c d hc hd A.coefficientProfile
      (by simpa [c, d] using hzero) hfirst
  exact ⟨contactOrder, A, hkgt, hklt, hjgt, hjlt,
    by simpa [c, d] using hEuler⟩

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
