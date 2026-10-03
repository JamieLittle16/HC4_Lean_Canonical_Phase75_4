import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitZeroSchur
import HC4.Newton.RankOneSingularSchurContinuation
import Mathlib.Tactic

/-!
# Continue the central zero-Schur tail past its first rank-one pivot

The complete central total-deficit family has identically zero cleared Schur
determinant.  The first nonzero Schur layer was already normalized to a
nonzero determinant-zero binary tail and split into a left or right-axis
constant pivot.

This file performs only the constant binary alignment and then applies the
state-free singular rank-one continuation theorem.  The result retains the
pivot provenance and exposes the exact next dichotomy:

* stationary transverse tail: both aligned transverse entries vanish
  identically; or
* reflected interaction: a first off-diagonal order `j > 0`, no kernel
  coefficient below `2*j`, and a nonzero kernel coefficient at `2*j`
  satisfying the exact square identity.

No repair state, auxiliary clock, or source-coordinate identification is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- **Aligned continuation of the complete central zero-Schur tail.**

The returned series remembers whether it came from the left or right-axis
constant pivot.  Its determinant is still identically zero, and it is either
stationary in the transverse directions or carries the exact first reflected
`j,2*j` interaction.
-/
theorem centralDeficitZeroSchurTail_alignedContinuation
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    ∃ A : RankOneSchurSeries (MvPolynomial (Fin 4) K),
      A.leading ≠ 0 ∧
      A.determinant = 0 ∧
      ((∃ hleft : (Z.tailSeries hz).LeftPivot,
          A = (Z.tailSeries hz).alignLeft hleft) ∨
        (∃ hright : (Z.tailSeries hz).RightAxisPivot,
          A = (Z.tailSeries hz).alignRight hright)) ∧
      ((A.offDiag = 0 ∧ A.kernel = 0) ∨
        ∃ j : ℕ,
          0 < j ∧
          A.offDiag.coeff j ≠ 0 ∧
          (∀ n : ℕ, n < 2 * j → A.kernel.coeff n = 0) ∧
          A.leading * A.kernel.coeff (2 * j) =
            A.offDiag.coeff j * A.offDiag.coeff j ∧
          A.kernel.coeff (2 * j) ≠ 0) := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let Q := Z.tailSeries hz

  have hQdet : Q.determinant = 0 := by
    have h :=
      G.centralDeficitZeroSchurTail_determinant_eq_zero
        hthree houtThree
    simpa [Z, hz, Q] using h

  have hpivot :
      Q.LeftPivot ∨ Q.RightAxisPivot := by
    have h := G.centralDeficitZeroSchurTail_pivot hthree houtThree
    simpa [Z, hz, Q] using h

  rcases hpivot with hleft | hright
  · let A := Q.alignLeft hleft
    have hlead : A.leading ≠ 0 := by
      simpa [A] using Q.alignLeft_leading_ne_zero hleft
    have hdetA : A.determinant = 0 := by
      calc
        A.determinant =
            (Polynomial.C (Q.active.coeff 0)) ^ 2 * Q.determinant := by
              simpa [A] using Q.alignLeft_determinant hleft
        _ = 0 := by rw [hQdet]; simp
    have hcont :=
      A.stationary_or_reflectedInteraction hlead hdetA
    refine ⟨A, hlead, hdetA, ?_, hcont⟩
    left
    exact ⟨hleft, rfl⟩

  · let A := Q.alignRight hright
    have hlead : A.leading ≠ 0 := by
      simpa [A] using Q.alignRight_leading_ne_zero hright
    have hdetA : A.determinant = 0 := by
      calc
        A.determinant = Q.determinant := by
          simpa [A] using Q.alignRight_determinant hright
        _ = 0 := hQdet
    have hcont :=
      A.stationary_or_reflectedInteraction hlead hdetA
    refine ⟨A, hlead, hdetA, ?_, hcont⟩
    right
    exact ⟨hright, rfl⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
