import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly
import HC4.Polynomial.MonomialHessianPrincipalMinor
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# Collapse the `.pr` highest-slice branch to a pure-axis singleton

The complete nontrivial `.pr` finite-staircase assembly sends every
nontrivial highest pair slice to an actual rank-two Hessian chart on the
represented state.  Thus the only remaining highest-slice shape is a literal
singleton.

A singleton highest slice with two positive coordinates already has a nonzero
principal Hessian minor by the generic monomial theorem.  Two applications of
maximal-initial minor transport lift that minor first to the planar carrier and
then to the represented special fibre.  Since the `.pr` pair degree is
`d₀+d₁>1`, the only singleton shapes which do not immediately expose such a
minor are pure powers in coordinate `0` or coordinate `1`.

This file is a splice layer only.  It introduces no new clock, no repair-only
progress, and no extra algebraic hypothesis.
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

/-- A singleton highest-slice monomial with two positive coordinates gives the
same nonzero principal minor on the actual represented special fibre. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.singleton_sourceMinor_of_two_positive
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d})
    {i j : Fin 4}
    (hij : i ≠ j)
    (hi : 0 < d i)
    (hj : 0 < d j) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        i j ≠ 0 := by
  classical
  have hd : d ∈ S.slice.support := by
    rw [hsupp]
    simp
  have hcoeff : MvPolynomial.coeff d S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hmono :
      S.slice = MvPolynomial.monomial d (MvPolynomial.coeff d S.slice) := by
    have hsum := MvPolynomial.as_sum S.slice
    rw [hsupp] at hsum
    simpa using hsum
  have hslice :
      HC4.Polynomial.hessianPrincipalMinor S.slice i j ≠ 0 := by
    rw [hmono]
    exact HC4.Polynomial.hessianPrincipalMinor_monomial_ne_zero_of_two_positive
      hcoeff hij hi hj
  have hcarrier :
      HC4.Polynomial.hessianPrincipalMinor P.carrier i j ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      S.carrier_pair_bound i j
    rw [← S.slice_eq_initialForm]
    exact hslice
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    P.source_bound i j
  rw [← P.carrier_eq_initialForm]
  exact hcarrier

private noncomputable def actualRankTwoChart01
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (0 : Fin 4) (1 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) := Equiv.refl (Fin 4)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart02
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (0 : Fin 4) (2 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart03
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (0 : Fin 4) (3 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart12
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (1 : Fin 4) (2 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

private noncomputable def actualRankTwoChart13
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (h : HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber s.family) (1 : Fin 4) (3 : Fin 4) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using h

/-- A singleton `.pr` highest slice either already exposes actual rank-two
geometry or is a literal pure power in one of the two pair coordinates. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_singleton_actualRankTwo_or_pureAxis
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    {d : Fin 4 →₀ ℕ}
    (hsupp : S.slice.support = {d}) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      ((1 < d 0 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0) ∨
       (1 < d 1 ∧ d 0 = 0 ∧ d 2 = 0 ∧ d 3 = 0)) := by
  classical
  have hd : d ∈ S.slice.support := by
    rw [hsupp]
    simp
  have hpair := (S.support_parent_and_pairLevel hd).2
  have hlevel :
      (1 : ℤ) < (d 0 : ℤ) + (d 1 : ℤ) := by
    rw [← hpair]
    simpa [qsOtherFacetPairDegree] using S.pairLevel_gt_one
  by_cases h0 : 0 < d 0
  · by_cases h1 : 0 < d 1
    · have hm := S.singleton_sourceMinor_of_two_positive hsupp
          (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) h0 h1
      exact Or.inl ⟨actualRankTwoChart01 hm⟩
    · have h1z : d 1 = 0 := Nat.eq_zero_of_not_pos h1
      by_cases h2 : 0 < d 2
      · have hm := S.singleton_sourceMinor_of_two_positive hsupp
            (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) h0 h2
        exact Or.inl ⟨actualRankTwoChart02 hm⟩
      · have h2z : d 2 = 0 := Nat.eq_zero_of_not_pos h2
        by_cases h3 : 0 < d 3
        · have hm := S.singleton_sourceMinor_of_two_positive hsupp
              (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide) h0 h3
          exact Or.inl ⟨actualRankTwoChart03 hm⟩
        · have h3z : d 3 = 0 := Nat.eq_zero_of_not_pos h3
          have h0gt : 1 < d 0 := by
            have h0z : (1 : ℤ) < (d 0 : ℤ) := by simpa [h1z] using hlevel
            exact_mod_cast h0z
          exact Or.inr (Or.inl ⟨h0gt, h1z, h2z, h3z⟩)
  · have h0z : d 0 = 0 := Nat.eq_zero_of_not_pos h0
    have h1gt : 1 < d 1 := by
      have h1z : (1 : ℤ) < (d 1 : ℤ) := by simpa [h0z] using hlevel
      exact_mod_cast h1z
    have h1pos : 0 < d 1 := by omega
    by_cases h2 : 0 < d 2
    · have hm := S.singleton_sourceMinor_of_two_positive hsupp
          (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide) h1pos h2
      exact Or.inl ⟨actualRankTwoChart12 hm⟩
    · have h2z : d 2 = 0 := Nat.eq_zero_of_not_pos h2
      by_cases h3 : 0 < d 3
      · have hm := S.singleton_sourceMinor_of_two_positive hsupp
            (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide) h1pos h3
        exact Or.inl ⟨actualRankTwoChart13 hm⟩
      · have h3z : d 3 = 0 := Nat.eq_zero_of_not_pos h3
        exact Or.inr (Or.inr ⟨h1gt, h0z, h2z, h3z⟩)

/-- **`.pr` highest-slice closure up to pure-axis special fibre.**
Starting from the actual other-facet endpoint, every nontrivial highest pair
slice and every two-coordinate singleton gives an actual rank-two chart.  The
only survivor is a pure power in coordinate `0` or coordinate `1`. -/
theorem qs_ray_pr_actualRankTwo_or_pureAxisHighestSlice
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      ∃ P : QsOtherFacetPlanarCarrierPackage C .pr,
        ∃ S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P,
          ∃ d : Fin 4 →₀ ℕ,
            S.slice.support = {d} ∧
              ((1 < d 0 ∧ d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0) ∨
               (1 < d 1 ∧ d 0 = 0 ∧ d 2 = 0 ∧ d 3 = 0)) := by
  classical
  rcases C.qs_ray_otherFacet_planarHighestPairSlice_package
      hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree with
    ⟨P, hS⟩
  rcases hS with ⟨S⟩
  by_cases hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b
  · exact Or.inl
      (S.pr_nontrivial_actualRankTwoHessianChart
        hthree houtThree hnontrivial)
  · have hsuppNonempty : S.slice.support.Nonempty :=
      MvPolynomial.support_nonempty.mpr S.slice_ne_zero
    rcases hsuppNonempty with ⟨d, hd⟩
    have hsupp : S.slice.support = {d} := by
      ext e
      constructor
      · intro he
        have hed : e = d := by
          by_contra hne
          apply hnontrivial
          exact ⟨e, he, d, hd, hne⟩
        simpa [hed]
      · intro he
        simp only [Finset.mem_singleton] at he
        subst e
        exact hd
    rcases S.pr_singleton_actualRankTwo_or_pureAxis hsupp with htwo | hpure
    · exact Or.inl htwo
    · exact Or.inr ⟨P, S, d, hsupp, hpure⟩

/-- Earlier, weaker boundary-singleton form retained for downstream callers
which only need boundary information. -/
theorem qs_ray_pr_actualRankTwo_or_singletonHighestSlice
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      ∃ P : QsOtherFacetPlanarCarrierPackage C .pr,
        ∃ S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P,
          ∃ d : Fin 4 →₀ ℕ,
            S.slice.support = {d} ∧
              HC4.Polynomial.MvExponentOnBoundary d := by
  rcases C.qs_ray_pr_actualRankTwo_or_pureAxisHighestSlice hthree houtThree with
    htwo | hpure
  · exact Or.inl htwo
  · rcases hpure with ⟨P, S, d, hsupp, hpure⟩
    refine Or.inr ⟨P, S, d, hsupp, ?_⟩
    rcases hpure with h0 | h1
    · exact ⟨1, h0.2.1⟩
    · exact ⟨0, h1.2.1⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
