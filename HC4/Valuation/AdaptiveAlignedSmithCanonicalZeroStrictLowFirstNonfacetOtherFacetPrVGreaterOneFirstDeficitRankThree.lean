import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSingleton
import HC4.Polynomial.RankTwoToRankThreeRoofLinearCoefficient
import Mathlib.Tactic

/-!
# The first central-deficit layer genuinely raises the Hessian rank to three

The source-honest total-deficit Rees family has

* an exact rank-two constant Hessian block on source coordinates `0,3`;
* no positive parameter layer below the canonical first deficit order; and
* a first binary deficit face which is a nonzero pure-axis linear-form power
  of degree at least two.

Hence the Hessian diagonal in that pure axis is nonzero.  Restricting the
complete binary parameter Hessian to coordinates `(0,1,3)` or `(0,2,3)`,
the generic rank-two-to-rank-three gap criterion shows that the corresponding
three-by-three determinant series is nonzero.

This is genuine geometry of the represented source family.  No repair label
is changed and no auxiliary Rees order is identified with the blocker clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Ambient coordinates `0,1,3`, with the first deficit axis in the middle. -/
def firstDeficitOneRoofIndex : Fin 3 → Fin 4 := ![0, 1, 3]

/-- Ambient coordinates `0,2,3`, with the second deficit axis in the middle. -/
def firstDeficitTwoRoofIndex : Fin 3 → Fin 4 := ![0, 2, 3]

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

/-- A nonzero coordinate of a binary linear form gives a nonzero diagonal
Hessian entry of every scalar multiple of its power of degree at least two. -/
private theorem binaryLinearPower_hessian_diag_ne_zero
    {a : K} {c : Fin 2 → K} {q : ℕ} {i : Fin 2}
    (hq : 2 ≤ q) (ha : a ≠ 0) (hci : c i ≠ 0) :
    HC4.Polynomial.hessian
      (MvPolynomial.C a * (gradientRatioLinearForm c) ^ q) i i ≠ 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q = n + 2 := by
    exact ⟨q - 2, by omega⟩
  subst q
  rw [HC4.Valuation.hessian_C_mul_gradientRatioLinearForm_pow_add_two]
  have hn2 : (((n + 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hn1 : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hL : gradientRatioLinearForm c ≠ 0 := by
    intro hzero
    have hder :=
      HC4.Valuation.pderiv_gradientRatioLinearForm_fin
        (K := K) c i
    rw [hzero] at hder
    have hci0 : c i = 0 := by
      simpa using hder
    exact hci hci0
  have hscalar :
      a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) * c i * c i ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact ha
    · exact hn2
    · exact hn1
    · exact hci
    · exact hci
  exact mul_ne_zero
    (MvPolynomial.C_ne_zero.mpr hscalar)
    (pow_ne_zero _ hL)

/-- Three-by-three parameter Hessian on ambient coordinates `0,1,3`. -/
noncomputable def firstDeficitOneRoofHessian :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  fun i j =>
    binaryParameterHessian G
      (firstDeficitOneRoofIndex i)
      (firstDeficitOneRoofIndex j)

/-- Three-by-three parameter Hessian on ambient coordinates `0,2,3`. -/
noncomputable def firstDeficitTwoRoofHessian :
    Matrix (Fin 3) (Fin 3)
      (Polynomial (MvPolynomial (Fin 2) K)) :=
  fun i j =>
    binaryParameterHessian G
      (firstDeficitTwoRoofIndex i)
      (firstDeficitTwoRoofIndex j)

private theorem oneRoof_gap
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow (firstDeficitOrder G)
      (G.firstDeficitOneRoofHessian i j) := by
  exact binaryParameterHessian_gap G _ _

private theorem twoRoof_gap
    (i j : Fin 3) :
    HasNoPositiveParameterCoeffBelow (firstDeficitOrder G)
      (G.firstDeficitTwoRoofHessian i j) := by
  exact binaryParameterHessian_gap G _ _

private theorem oneRoof_base
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i j : Fin 3) :
    (G.firstDeficitOneRoofHessian i j).coeff 0 =
      HC4.Polynomial.rankTwoRoofZeroKernelBase
        (centralBinaryCore G 0 0) (centralBinaryCore G 0 3)
        (centralBinaryCore G 3 0) (centralBinaryCore G 3 3) i j := by
  have h0 := binaryParameterHessian_coeff_zero G hthree houtThree
  have hcore := centralBinaryCore_eq_rankTwoBase G
  have hentry :=
    congrFun (congrFun h0 (firstDeficitOneRoofIndex i))
      (firstDeficitOneRoofIndex j)
  rw [hcore] at hentry
  fin_cases i <;> fin_cases j <;>
    simpa [firstDeficitOneRoofHessian, firstDeficitOneRoofIndex,
      HC4.Polynomial.rankTwoRoofZeroKernelBase,
      HC4.Polynomial.rankTwoZeroKernelBase] using hentry

private theorem twoRoof_base
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i j : Fin 3) :
    (G.firstDeficitTwoRoofHessian i j).coeff 0 =
      HC4.Polynomial.rankTwoRoofZeroKernelBase
        (centralBinaryCore G 0 0) (centralBinaryCore G 0 3)
        (centralBinaryCore G 3 0) (centralBinaryCore G 3 3) i j := by
  have h0 := binaryParameterHessian_coeff_zero G hthree houtThree
  have hcore := centralBinaryCore_eq_rankTwoBase G
  have hentry :=
    congrFun (congrFun h0 (firstDeficitTwoRoofIndex i))
      (firstDeficitTwoRoofIndex j)
  rw [hcore] at hentry
  fin_cases i <;> fin_cases j <;>
    simpa [firstDeficitTwoRoofHessian, firstDeficitTwoRoofIndex,
      HC4.Polynomial.rankTwoRoofZeroKernelBase,
      HC4.Polynomial.rankTwoZeroKernelBase] using hentry

/-- If the first Hesse axis is source coordinate `1`, its roof minor is
genuinely rank three over the parameter series. -/
theorem firstDeficitOneRoofHessian_det_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {a : K} {c : Fin 2 → K}
    (hface :
      firstDeficitBinaryFace G =
        MvPolynomial.C a *
          (gradientRatioLinearForm c) ^ (firstDeficitOrder G))
    (ha : a ≠ 0)
    (hc0 : c 0 ≠ 0) :
    G.firstDeficitOneRoofHessian.det ≠ 0 := by
  have hdiagBinary :
      HC4.Polynomial.hessian (firstDeficitBinaryFace G)
        (0 : Fin 2) 0 ≠ 0 := by
    rw [hface]
    exact binaryLinearPower_hessian_diag_ne_zero
      (firstDeficitOrder_two_le G hthree houtThree) ha hc0
  have hdiag :
      (G.firstDeficitOneRoofHessian 1 1).coeff
          (firstDeficitOrder G) ≠ 0 := by
    change
      (binaryParameterHessian G 1 1).coeff
          (firstDeficitOrder G) ≠ 0
    rw [binaryParameterHessian_coeff G]
    rw [← HC4.Polynomial.hessian_zero_zero_centralDeficitBinarySpecialisation]
    simpa [firstDeficitBinaryFace, firstDeficitLayer] using hdiagBinary
  exact
    HC4.Polynomial.polynomialMatrix3_gap_det_ne_zero_of_middleDiagonal
      (firstDeficitOrder_pos G)
      G.firstDeficitOneRoofHessian
      (fun i j => G.oneRoof_gap i j)
      (centralBinaryCore G 0 0) (centralBinaryCore G 0 3)
      (centralBinaryCore G 3 0) (centralBinaryCore G 3 3)
      (fun i j => G.oneRoof_base hthree houtThree i j)
      (centralBinaryCore_activeDet_ne_zero G hthree houtThree)
      hdiag

/-- If the first Hesse axis is source coordinate `2`, its roof minor is
genuinely rank three over the parameter series. -/
theorem firstDeficitTwoRoofHessian_det_ne_zero
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {a : K} {c : Fin 2 → K}
    (hface :
      firstDeficitBinaryFace G =
        MvPolynomial.C a *
          (gradientRatioLinearForm c) ^ (firstDeficitOrder G))
    (ha : a ≠ 0)
    (hc1 : c 1 ≠ 0) :
    G.firstDeficitTwoRoofHessian.det ≠ 0 := by
  have hdiagBinary :
      HC4.Polynomial.hessian (firstDeficitBinaryFace G)
        (1 : Fin 2) 1 ≠ 0 := by
    rw [hface]
    exact binaryLinearPower_hessian_diag_ne_zero
      (firstDeficitOrder_two_le G hthree houtThree) ha hc1
  have hdiag :
      (G.firstDeficitTwoRoofHessian 1 1).coeff
          (firstDeficitOrder G) ≠ 0 := by
    change
      (binaryParameterHessian G 2 2).coeff
          (firstDeficitOrder G) ≠ 0
    rw [binaryParameterHessian_coeff G]
    rw [← HC4.Polynomial.hessian_one_one_centralDeficitBinarySpecialisation]
    simpa [firstDeficitBinaryFace, firstDeficitLayer] using hdiagBinary
  exact
    HC4.Polynomial.polynomialMatrix3_gap_det_ne_zero_of_middleDiagonal
      (firstDeficitOrder_pos G)
      G.firstDeficitTwoRoofHessian
      (fun i j => G.twoRoof_gap i j)
      (centralBinaryCore G 0 0) (centralBinaryCore G 0 3)
      (centralBinaryCore G 3 0) (centralBinaryCore G 3 3)
      (fun i j => G.twoRoof_base hthree houtThree i j)
      (centralBinaryCore_activeDet_ne_zero G hthree houtThree)
      hdiag

/-- **Source-honest first-deficit rank-three alternative.**  The complete
central Rees family has a genuinely nonzero three-by-three roof minor in the
same orientation selected by binary Hesse rigidity. -/
theorem firstDeficit_rankThree_roof
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.firstDeficitOneRoofHessian.det ≠ 0 ∨
      G.firstDeficitTwoRoofHessian.det ≠ 0 := by
  rcases firstDeficitBinaryFace_pureAxis G hthree houtThree with
    ⟨a, c, hface, ha, haxis⟩
  rcases haxis with hzero | hone
  · exact Or.inl
      (G.firstDeficitOneRoofHessian_det_ne_zero
        hthree houtThree hface ha hzero.1)
  · exact Or.inr
      (G.firstDeficitTwoRoofHessian_det_ne_zero
        hthree houtThree hface ha hone.2)

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
