import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly
import Mathlib.Tactic

/-!
# Collapse the `.pr` highest-slice branch to a boundary singleton

The complete nontrivial `.pr` finite-staircase assembly now sends every
nontrivial highest pair slice to an actual rank-two Hessian chart on the
represented state.  Thus the only surviving highest-slice shape is a literal
singleton.  The source-honest highest-slice theorem already shows that such a
singleton lies on the coordinate boundary.

This is a splice theorem only: it introduces no new clock, no repair-only
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

/-- **`.pr` highest-slice closure up to the singleton boundary case.**
Starting from the actual other-facet endpoint, either the already-existing
actual rank-two Hessian chart is obtained, or the source-honest highest pair
slice is literally one boundary monomial. -/
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
    exact Or.inr ⟨P, S, d, hsupp, S.singleton_on_boundary hsupp⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
