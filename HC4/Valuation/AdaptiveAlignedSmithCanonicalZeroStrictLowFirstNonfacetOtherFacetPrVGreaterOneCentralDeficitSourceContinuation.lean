import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitZeroSchur
import HC4.Newton.RankOneSingularSchurConstantKernel
import HC4.Newton.GeneralFourBlockKernelLift
import Mathlib.Tactic

/-!
# Source-safe continuation of the central zero-Schur tail

The normalized central Schur tail has a nonzero determinant-zero constant
block.  The generic binary dispatcher now gives exactly two outcomes.

* **Stationary:** pull the aligned stationary kernel back to the raw binary
  Schur coordinates.  Restoring the common first parameter factor gives a
  cleared Schur kernel of the original complete central four-block.  The
  generic denominator-cleared lift then gives an honest four-coordinate
  polynomial kernel equation for that original Hessian block.
* **Reflected:** retain the aligned first transverse order `j`, its nonzero
  off-diagonal coefficient, and the forced nonzero kernel coefficient at
  `2*j`.

The alignment is used only inside the generic binary algebra.  It is never
declared to be a source-coordinate transformation.
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

/-- The active `(0,3)` determinant of the complete central block is
nonzero as a polynomial series.  Its constant coefficient is exactly the
retained nonzero principal minor of the honest coordinate-max central face. -/
theorem centralDeficitSchurBlock_activeDet_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.activeDet ≠ 0 := by
  have hlayer0 :
      familyParameterLayer P.centralDeficitFamily 0 = G.exposure.face := by
    calc
      familyParameterLayer P.centralDeficitFamily 0 =
          MvPolynomial.monomial G.central
            (MvPolynomial.coeff G.central P.carrier) :=
        G.centralDeficitFamily_layer_zero_eq hthree houtThree
      _ = G.exposure.face := G.exposure_face_eq.symm
  have hcoeff :
      G.centralDeficitSchurBlock.activeDet.coeff 0 ≠ 0 := by
    unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
    unfold GeneralFourBlock.activeDet
    rw [permutedFamilyHessianFourBlock_a,
      permutedFamilyHessianFourBlock_b,
      permutedFamilyHessianFourBlock_d]
    simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
    rw [centralDeficitActiveDet_coeff_zero_eq]
    rw [hlayer0]
    exact G.exposure_rankTwo_minor
  intro hzero
  rw [hzero] at hcoeff
  simp at hcoeff

/-- **Raw-kernel or reflected continuation of the central total-deficit
family.**

The stationary branch is stated entirely in the raw source-honest central
four-block.  In particular the returned binary kernel coordinates are
polynomials in the source variables but are constant in the Rees parameter.
-/
theorem centralDeficit_rawKernel_or_reflectedInteraction
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := G.centralDeficitSchurBlock
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    let Q := Z.tailSeries hz
    (∃ u v : MvPolynomial (Fin 4) K,
        (u ≠ 0 ∨ v ≠ 0) ∧
        H.IsClearedSchurKernel (Polynomial.C u) (Polynomial.C v) ∧
        H.clearedKernelLift (Polynomial.C u) (Polynomial.C v) ≠ 0 ∧
        H.matrix.mulVec
          (H.clearedKernelLift (Polynomial.C u) (Polynomial.C v)) = 0) ∨
      ∃ A : RankOneSchurSeries (MvPolynomial (Fin 4) K),
        A.leading ≠ 0 ∧
        A.determinant = 0 ∧
        ((∃ hleft : Q.LeftPivot, A = Q.alignLeft hleft) ∨
          (∃ hright : Q.RightAxisPivot, A = Q.alignRight hright)) ∧
        ∃ j : ℕ,
          0 < j ∧
          A.offDiag.coeff j ≠ 0 ∧
          (∀ n : ℕ, n < 2 * j → A.kernel.coeff n = 0) ∧
          A.leading * A.kernel.coeff (2 * j) =
            A.offDiag.coeff j * A.offDiag.coeff j ∧
          A.kernel.coeff (2 * j) ≠ 0 := by
  let H := G.centralDeficitSchurBlock
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let Q := Z.tailSeries hz

  have hQdet : Q.determinant = 0 := by
    have h :=
      G.centralDeficitZeroSchurTail_determinant_eq_zero
        hthree houtThree
    simpa [Z, hz, Q] using h

  have hpivot : Q.LeftPivot ∨ Q.RightAxisPivot := by
    have h := G.centralDeficitZeroSchurTail_pivot hthree houtThree
    simpa [Z, hz, Q] using h

  rcases Q.constantKernel_or_reflectedInteraction hQdet hpivot with
    hconstant | hreflected
  · left
    rcases hconstant with ⟨u, v, huv, hrawA, hrawB⟩
    have hfactorA := Z.active_eq_firstFactor_mul_tail hz
    have hfactorB := Z.offDiag_eq_firstFactor_mul_tail hz
    have hfactorC := Z.kernel_eq_firstFactor_mul_tail hz
    have hA :
        H.schurA =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.active := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorA
    have hB :
        H.schurB =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorB
    have hC :
        H.schurC =
          Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.kernel := by
      simpa [H, Z, Q, centralDeficitZeroSchurSeries,
        GeneralFourBlock.polynomialSchurSeries] using hfactorC
    have hker :
        H.IsClearedSchurKernel (Polynomial.C u) (Polynomial.C v) := by
      unfold GeneralFourBlock.IsClearedSchurKernel
      constructor
      · rw [hA, hB]
        calc
          (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.active) *
                Polynomial.C u +
              (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag) *
                Polynomial.C v =
            Polynomial.X ^ Z.firstPositiveEntryOrder hz *
              (Q.active * Polynomial.C u +
                Q.offDiag * Polynomial.C v) := by ring
          _ = 0 := by rw [hrawA]; simp
      · rw [hB, hC]
        calc
          (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.offDiag) *
                Polynomial.C u +
              (Polynomial.X ^ Z.firstPositiveEntryOrder hz * Q.kernel) *
                Polynomial.C v =
            Polynomial.X ^ Z.firstPositiveEntryOrder hz *
              (Q.offDiag * Polynomial.C u +
                Q.kernel * Polynomial.C v) := by ring
          _ = 0 := by rw [hrawB]; simp
    have hactive : H.activeDet ≠ 0 := by
      simpa [H] using
        G.centralDeficitSchurBlock_activeDet_ne_zero hthree houtThree
    have huvC :
        Polynomial.C u ≠ 0 ∨ Polynomial.C v ≠ 0 := by
      rcases huv with hu | hv
      · exact Or.inl (Polynomial.C_ne_zero.mpr hu)
      · exact Or.inr (Polynomial.C_ne_zero.mpr hv)
    have hlift :
        H.clearedKernelLift (Polynomial.C u) (Polynomial.C v) ≠ 0 :=
      H.clearedKernelLift_ne_zero_of_activeDet_ne_zero
        (Polynomial.C u) (Polynomial.C v) hactive huvC
    refine Or.inl ⟨u, v, huv, hker, hlift, ?_⟩
    exact H.mulVec_clearedKernelLift_eq_zero
      (Polynomial.C u) (Polynomial.C v) hker
  · exact Or.inr hreflected

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
