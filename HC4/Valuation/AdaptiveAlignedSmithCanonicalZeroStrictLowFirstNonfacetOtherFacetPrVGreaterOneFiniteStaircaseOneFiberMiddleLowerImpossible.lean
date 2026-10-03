import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberMiddleTop
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneEndpointFibers
import HC4.Newton.MixedDegreeWallRefinement
import HC4.Polynomial.UniqueMaximalInitialMonomial
import HC4.Polynomial.MonomialHessian
import Mathlib.Tactic

/-!
# A19 middle lower-degree one-fibre branch is impossible

On the middle diagonal `j+1=k`, suppose the honest interior profile has degree
`k-1`.  The top profile coefficient gives an actual source monomial

    d = (k-1,1,1,V*k).

The staircase wall rules out `k=2`, hence `k-1>1`.  In the one-fibre branch
every strict-interior source monomial lies in the same selected pair fibre, so
its longitudinal coordinate occurs in the common coefficient profile and is
at most `k-1`.  The locked and highest endpoint fibres have longitudinal
coordinate only `0` or `1`.  Thus `d` is the unique maximal longitudinal
source monomial.

The maximal-longitudinal initial of the singular carrier is therefore exactly
the monomial `d`; maximal-initial singularity says its Hessian determinant is
zero, while the monomial Hessian formula makes it nonzero because every
coordinate of `d` is positive.  Contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free arithmetic used only to separate the middle lower top degree
from the endpoint degree one. -/
theorem middle_oneFiber_k_three_le_of_wall
    {n ell k : ℕ}
    (hn : 2 ≤ n) (hnell : n ≤ ell)
    (hk : 1 < k) (hkn : k < n)
    (hwall :
      ((n : ℤ) - 1) * ((k : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    3 ≤ k := by
  by_contra hnot
  have hk2 : k = 2 := by omega
  have hn3 : 3 ≤ n := by omega
  have hwallNat : (n - 1) * (k - 1) = ell * (n - k) := by
    have hn1 : 1 ≤ n := by omega
    have hkle : k ≤ n := by omega
    have hk1 : 1 ≤ k := by omega
    rw [← Nat.cast_sub hn1, ← Nat.cast_sub hk1,
      ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_sub hkle] at hwall
    exact_mod_cast hwall
  rw [hk2] at hwallNat
  norm_num at hwallNat
  have hgap : 1 ≤ n - 2 := by omega
  have hmul : ell ≤ ell * (n - 2) := by
    simpa using Nat.mul_le_mul_left ell hgap
  omega

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

/-- **Middle lower-degree elimination.** -/
theorem oneFiber_middle_lower_degree_impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 1 = Alo.k)
    (hdeg : Alo.coefficientProfile.natDegree = Alo.k - 1) : False := by
  rcases F.exists_middleLower_top_carrierExponent Alo hdiag hdeg with
    ⟨d, hdP, hd0, hd1, hd2, hd3⟩

  have hs := F.support_staircase_equations hthree houtThree hdP
  have hwall :
      ((F.highest.n : ℤ) - 1) * ((Alo.k : ℤ) - 1) =
        (F.locked.ell : ℤ) *
          ((F.highest.n : ℤ) - (Alo.k : ℤ)) := by
    have h := hs.1
    simp only [rankThreeQuotientCoordinate_pair,
      rankThreeQuotientCoordinate_firstTransverse] at h
    rw [hd0, hd1, hd2] at h
    push_cast at h
    norm_num at h ⊢
    nlinarith
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hk3 : 3 ≤ Alo.k :=
    middle_oneFiber_k_three_le_of_wall
      F.highest.n_two_le hnell Alo.k_gt_one Alo.k_lt_highest hwall
  have hmgt1 : 1 < Alo.k - 1 := by omega

  have hprofiles := F.selectedInteriorProfiles_eq_of_k_eq
    Alo Ahi hthree houtThree hext

  have hlongBound : ∀ e ∈ P.carrier.support, e 0 ≤ Alo.k - 1 := by
    intro e heP
    have hpairPos := F.support_pair_pos hthree houtThree heP
    rcases F.support_staircase_classification hthree houtThree heP with
      ⟨j, _hj, hpairLe, _hjLe, hjZero, hjLocked⟩
    let pair := (rankThreeQuotientCoordinate 1 F.V e).pair
    by_cases hlock : pair = 1
    · rcases F.eq_locked_of_support_pair_eq_one heP hlock with rfl | rfl
      · rw [F.locked.facet_zero]
        omega
      · rw [F.locked.outside_zero]
        omega
    by_cases hhigh : pair = F.highest.n
    · rcases F.eq_highest_of_support_pair_eq_n heP hhigh with rfl | rfl
      · rw [F.highest.e0_zero]
        omega
      · rw [F.highest.e1_zero]
        omega
    · have hgt : 1 < pair := by
        dsimp [pair]
        omega
      have hlt : pair < F.highest.n := by
        dsimp [pair]
        omega
      have hpairEq := F.strictInterior_pair_eq_of_extrema_eq
        Alo Ahi hthree houtThree hnot hext heP hgt hlt
      have heLayer :
          e ∈ (familyParameterLayer D.family
            (firstPositiveActualParameterOrder D.family D.positiveLayer)).support := by
        rw [Ahi.firstPositiveLayer_support_eq_pairFiber hthree houtThree]
        exact Finset.mem_filter.mpr ⟨heP, hpairEq.trans hext⟩
      have hprofHi : Ahi.coefficientProfile.coeff (e 0) ≠ 0 := by
        rw [Ahi.coeff_coefficientProfile_of_mem heLayer]
        exact MvPolynomial.mem_support_iff.mp heLayer
      have hprofLo : Alo.coefficientProfile.coeff (e 0) ≠ 0 := by
        rw [hprofiles]
        exact hprofHi
      have hle := Polynomial.le_natDegree_of_ne_zero hprofLo
      simpa [hdeg] using hle

  have hweightBound :
      HC4.Polynomial.IsWeightLE HC4.Newton.longitudinalIntegerWeight
        ((Alo.k - 1 : ℕ) : ℤ) P.carrier := by
    intro e heP
    rw [HC4.Newton.longitudinalIntegerWeight_eq]
    exact_mod_cast hlongBound e heP

  have hdweight :
      Finsupp.weight HC4.Newton.longitudinalIntegerWeight d =
        ((Alo.k - 1 : ℕ) : ℤ) := by
    rw [HC4.Newton.longitudinalIntegerWeight_eq, hd0]

  have huniq : ∀ e ∈ P.carrier.support,
      Finsupp.weight HC4.Newton.longitudinalIntegerWeight e =
        ((Alo.k - 1 : ℕ) : ℤ) → e = d := by
    intro e heP heWeight
    have he0 : e 0 = Alo.k - 1 := by
      rw [HC4.Newton.longitudinalIntegerWeight_eq] at heWeight
      exact_mod_cast heWeight
    have hpairPos := F.support_pair_pos hthree houtThree heP
    rcases F.support_staircase_classification hthree houtThree heP with
      ⟨j, _hj, hpairLe, _hjLe, _hjZero, _hjLocked⟩
    let pair := (rankThreeQuotientCoordinate 1 F.V e).pair
    have hnotLock : pair ≠ 1 := by
      intro hp
      rcases F.eq_locked_of_support_pair_eq_one heP hp with rfl | rfl
      · rw [F.locked.facet_zero] at he0
        omega
      · rw [F.locked.outside_zero] at he0
        omega
    have hnotHigh : pair ≠ F.highest.n := by
      intro hp
      rcases F.eq_highest_of_support_pair_eq_n heP hp with rfl | rfl
      · rw [F.highest.e0_zero] at he0
        omega
      · rw [F.highest.e1_zero] at he0
        omega
    have hgt : 1 < pair := by dsimp [pair]; omega
    have hlt : pair < F.highest.n := by dsimp [pair]; omega
    have hpairEq := F.strictInterior_pair_eq_of_extrema_eq
      Alo Ahi hthree houtThree hnot hext heP hgt hlt
    have heLayer :
        e ∈ (familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.positiveLayer)).support := by
      rw [Ahi.firstPositiveLayer_support_eq_pairFiber hthree houtThree]
      exact Finset.mem_filter.mpr ⟨heP, hpairEq.trans hext⟩
    have hdPair :
        (rankThreeQuotientCoordinate 1 F.V d).pair = Ahi.k := by
      simp [rankThreeQuotientCoordinate, hd0, hd1, ← hext]
    have hdLayer :
        d ∈ (familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.positiveLayer)).support := by
      rw [Ahi.firstPositiveLayer_support_eq_pairFiber hthree houtThree]
      exact Finset.mem_filter.mpr ⟨hdP, hdPair⟩
    exact Ahi.eq_of_zeroCoordinate_eq heLayer hdLayer (by omega)

  have hinit := HC4.Polynomial.initialForm_eq_monomial_of_unique_max
    HC4.Newton.longitudinalIntegerWeight ((Alo.k - 1 : ℕ) : ℤ)
    P.carrier d hdP hdweight hweightBound huniq

  have hsing :=
    HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
      HC4.Newton.longitudinalIntegerWeight ((Alo.k - 1 : ℕ) : ℤ)
      P.carrier hweightBound P.hessian_zero
  rw [hinit] at hsing

  have hc : MvPolynomial.coeff d P.carrier ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdP
  have hpos : ∀ i : Fin 4, 0 < d i := by
    intro i
    fin_cases i
    · rw [hd0]
      omega
    · rw [hd1]
      omega
    · rw [hd2]
      omega
    · rw [hd3]
      exact Nat.mul_pos (by omega) Alo.k_gt_one
  have hdeg3 : 3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
    simp [HC4.Polynomial.ordinaryDegree4, hd0, hd1, hd2, hd3]
    omega
  have hne := HC4.Polynomial.hessianDeterminant_monomial_ne_zero
    hc hpos hdeg3
  exact hne hsing

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
