import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralFirstLayerHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneAdjacentDeficit
import HC4.Polynomial.BinaryLinearPowerAdjacentSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreHesseBridge
import Mathlib.Tactic

/-!
# Linear-power rigidity of the first central-deficit layer

The previous module proves that the first positive total-deficit layer is an
honest nonzero homogeneous binary polynomial with zero Hessian determinant.
Binary Hesse rigidity therefore writes it as a scalar multiple of a power of
one linear form.

The source staircase excludes total deficit one, so the power has degree at
least two. If both coefficients of the linear form are nonzero, the pure
U^q and adjacent U^(q-1)V coefficients are both nonzero. The binary
support-lifting lemma returns two actual source monomials with adjacent deficit
pairs, contradicting the exact finite-staircase chord.

Hence the first positive total-deficit layer is necessarily a pure-axis
linear-form power. No auxiliary valuation clock or repair transition is used.
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

/-- The first positive total-deficit order cannot be one. -/
theorem firstDeficitOrder_two_le
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    2 ≤ firstDeficitOrder G := by
  have hpos := firstDeficitOrder_pos G
  by_contra hnot
  have hq : firstDeficitOrder G = 1 := by omega
  rcases MvPolynomial.support_nonempty.mpr (firstDeficitLayer_ne_zero G) with
    ⟨e, he⟩
  have heData := firstDeficitLayer_support G he
  have hcChord := F.support_deficit_chord hthree houtThree G.central_mem
  rw [G.central_one_zero, G.central_two_zero] at hcChord
  norm_num at hcChord
  have hunit : e 1 + e 2 = 1 := by
    simpa [hq] using heData.2
  exact HC4.Polynomial.no_unit_total_deficit_from_central_staircase_chord
    F.highest.n_two_le F.locked.ell_pos
    hcChord
    (F.support_deficit_chord hthree houtThree heData.1)
    hunit

/-- Binary Hesse rigidity applies to the first honest deficit face. -/
theorem firstDeficitBinaryFace_eq_linearPower
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ (a : K) (c : Fin 2 → K),
      firstDeficitBinaryFace G =
        MvPolynomial.C a *
          (gradientRatioLinearForm c) ^ (firstDeficitOrder G) := by
  exact HC4.Valuation.binaryHomogeneous_eq_linearFormPow_of_hessianDet_zero
    (firstDeficitBinaryFace G)
    (firstDeficitOrder G)
    (firstDeficitBinaryFace_isHomogeneous G)
    (firstDeficitBinaryFace_ne_zero G hthree houtThree)
    (firstDeficitOrder_two_le G hthree houtThree)
    (firstDeficitBinaryFace_hessian_zero G hthree houtThree)

/-- Both binary directions cannot occur in the Hesse linear form: they would
produce adjacent source deficit pairs on the same staircase. -/
theorem firstDeficitLinearPower_not_both_nonzero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {a : K} {c : Fin 2 → K}
    (hface :
      firstDeficitBinaryFace G =
        MvPolynomial.C a *
          (gradientRatioLinearForm c) ^ (firstDeficitOrder G))
    (hc0 : c 0 ≠ 0)
    (hc1 : c 1 ≠ 0) :
    False := by
  have ha : a ≠ 0 := by
    intro ha0
    apply firstDeficitBinaryFace_ne_zero G hthree houtThree
    rw [hface, ha0]
    simp
  let q := firstDeficitOrder G
  let m := q - 1
  have hq2 : 2 ≤ q := by
    dsimp [q]
    exact firstDeficitOrder_two_le G hthree houtThree
  have hqm : q = m + 1 := by
    dsimp [m]
    omega
  have hsupp :=
    HC4.Polynomial.pure_and_adjacent_mem_support_C_mul_linearPower
      (a := a) (c := c) (m := m) ha hc0 hc1
  have hpure :
      HC4.Polynomial.binaryPureZeroExponent q ∈
        (firstDeficitBinaryFace G).support := by
    rw [hface, hqm]
    simpa using hsupp.1
  have hadj :
      HC4.Polynomial.binaryAdjacentZeroOneExponent m ∈
        (firstDeficitBinaryFace G).support := by
    rw [hface, hqm]
    exact hsupp.2

  rcases
      HC4.Polynomial.exists_source_support_of_mem_centralDeficitBinarySpecialisation
        (firstDeficitLayer G) hpure with
    ⟨f, hf, hfproj⟩
  rcases
      HC4.Polynomial.exists_source_support_of_mem_centralDeficitBinarySpecialisation
        (firstDeficitLayer G) hadj with
    ⟨e, he, heproj⟩

  have hf1 := congrArg
    (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hfproj
  have hf2 := congrArg
    (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hfproj
  have he1 := congrArg
    (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) heproj
  have he2 := congrArg
    (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) heproj
  simp only [HC4.Polynomial.binaryDeficitExponent_zero,
    HC4.Polynomial.binaryDeficitExponent_one,
    HC4.Polynomial.binaryPureZeroExponent_zero_apply,
    HC4.Polynomial.binaryPureZeroExponent_one_apply,
    HC4.Polynomial.binaryAdjacentZeroOneExponent_zero_apply,
    HC4.Polynomial.binaryAdjacentZeroOneExponent_one_apply] at
      hf1 hf2 he1 he2

  have hfCarrier := (firstDeficitLayer_support G hf).1
  have heCarrier := (firstDeficitLayer_support G he).1
  have hf1adj : f 1 = e 1 + 1 := by
    dsimp [m] at he1
    omega
  have he2adj : e 2 = f 2 + 1 := by omega
  exact F.no_adjacent_deficits
    hthree houtThree heCarrier hfCarrier hf1adj he2adj

/-- Pure-axis first deficit layer: the Hesse linear form has exactly one
nonzero coordinate. -/
theorem firstDeficitBinaryFace_pureAxis
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ (a : K) (c : Fin 2 → K),
      firstDeficitBinaryFace G =
          MvPolynomial.C a *
            (gradientRatioLinearForm c) ^ (firstDeficitOrder G) ∧
      a ≠ 0 ∧
      ((c 0 ≠ 0 ∧ c 1 = 0) ∨ (c 0 = 0 ∧ c 1 ≠ 0)) := by
  rcases firstDeficitBinaryFace_eq_linearPower G hthree houtThree with
    ⟨a, c, hface⟩
  have ha : a ≠ 0 := by
    intro ha0
    apply firstDeficitBinaryFace_ne_zero G hthree houtThree
    rw [hface, ha0]
    simp
  by_cases hc0 : c 0 = 0
  · have hc1 : c 1 ≠ 0 := by
      intro hc1
      apply firstDeficitBinaryFace_ne_zero G hthree houtThree
      rw [hface, HC4.Polynomial.gradientRatioLinearForm_finTwo_eq]
      simp [hc0, hc1, firstDeficitOrder_pos G]
    exact ⟨a, c, hface, ha, Or.inr ⟨hc0, hc1⟩⟩
  · by_cases hc1 : c 1 = 0
    · exact ⟨a, c, hface, ha, Or.inl ⟨hc0, hc1⟩⟩
    · exact (firstDeficitLinearPower_not_both_nonzero
        G hthree houtThree hface hc0 hc1).elim

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
