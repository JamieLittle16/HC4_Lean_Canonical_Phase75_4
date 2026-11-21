import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayConstantSchurMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRaySchurWeightBounds
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyActiveConstant
import HC4.Valuation.ReverseReesAssociatedGraded

/-!
# An exact preterminal Schur clock on the actual PR ray Rees

The source, active pivot, nonzero constant Schur block and degree bounds all
come from the retained ray package. The output records the alignment with that
actual block. It makes no identification with the original zero-clock blocker
and asserts no global repair progress.
-/
namespace HC4.Valuation
noncomputable section
open HC4.Newton
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}

/-- The clock is retained together with its literal constant alignment. -/
theorem QsOtherFacetRayReverseReesPackage.pr_exists_exact_preterminal_schurClock
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hout : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := permutedFamilyHessianFourBlock qsPrSuperfaceSchurPermutation
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) R.bound)
    ∃ S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K),
      S.defect = 4 * R.level - 2 * ∑ i : Fin 4, R.weight i ∧
      ((∃ h : H.polynomialSchurSeries.LeftPivot,
          S.series = H.polynomialSchurSeries.alignLeft h) ∨
        (∃ h : H.polynomialSchurSeries.RightAxisPivot,
          S.series = H.polynomialSchurSeries.alignRight h)) ∧
      S.firstOrder < S.defect ∧ S.series.offDiag.coeff S.firstOrder ≠ 0 := by
  let F := reverseWeightedReesFamily R.weight R.level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) R.bound
  let H := permutedFamilyHessianFourBlock qsPrSuperfaceSchurPermutation F
  let D := 4 * R.level - 2 * ∑ i : Fin 4, R.weight i
  have hd : H.determinantCore = Polynomial.X ^ D :=
    permutedFamilyHessianFourBlock_determinantCore_eq_X_pow _ _ R.hessianDefect
  have ha : H.activeDet.coeff 0 ≠ 0 := by
    rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
    change HC4.Polynomial.hessianPrincipalMinor (polynomialFamilySpecialFiber F) 2 3 ≠ 0
    rw [R.specialFiber_eq_ray]
    intro hz
    have hn := C.qs_ray_pr_hessianPrincipalMinor_specialisation_coeff_two_ne_zero hthree hout
    rw [hz, map_zero, Polynomial.coeff_zero] at hn
    exact hn rfl
  have hc : H.schurC.coeff 0 ≠ 0 := R.pr_ray_schurC_coeff_zero_ne_zero hthree
  have hdet : H.polynomialSchurSeries.active.coeff 0 * H.polynomialSchurSeries.kernel.coeff 0 =
      H.polynomialSchurSeries.offDiag.coeff 0 * H.polynomialSchurSeries.offDiag.coeff 0 := by
    apply sub_eq_zero.mp
    have hz : H.polynomialSchurSeries.determinant.coeff 0 = 0 := by
      rw [H.polynomialSchurSeries_determinant, hd, Polynomial.coeff_mul_X_pow']
      simp [D, Nat.not_le_of_lt R.defect_pos]
    simpa [BinarySchurPolynomialSeries.determinant,
      Polynomial.coeff_zero_eq_eval_zero] using hz
  have hp := H.polynomialSchurSeries.leftPivot_or_rightAxisPivot_of_constantBlock
    (Or.inr (Or.inr hc)) hdet
  have hb : FourBlockParameterBudget H R.level
      (R.weight 2) (R.weight 3) (R.weight 0) (R.weight 1) :=
    reverseWeightedRees_fourBlockParameterBudget R.weight R.level _ R.bound _
  have hm := R.two_level_lt_defect
  rw [Fin.sum_univ_four] at hm
  have hw := R.pr_complementary_weights_lt_half_level hthree hout
  have hbound (S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (he : S.defect = D)
      (hz : S.series.offDiag.coeff D = 0 ∧ S.series.kernel.coeff D = 0) :
      S.firstOrder < S.defect := by
    have hl := S.firstOrder_le_defect
    by_contra hn
    have hf : S.firstOrder = D := by omega
    have ht := S.series.transverse_nonzero_at_first S.hasTransverse
    change S.series.offDiag.coeff S.firstOrder ≠ 0 ∨ S.series.kernel.coeff S.firstOrder ≠ 0 at ht
    rw [hf] at ht
    exact ht.elim (fun h => h hz.1) (fun h => h hz.2)
  rcases hp with hp | hp
  · let S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K) := {
      series := H.polynomialSchurSeries.alignLeft hp
      clearingFactor := Polynomial.C (H.schurA.coeff 0) ^ 2 * H.activeDet
      defect := D
      leading_ne_zero := H.polynomialSchurSeries.alignLeft_leading_ne_zero hp
      clearingFactor_coeff_zero_ne_zero := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        exact mul_ne_zero (pow_ne_zero 2 hp.1) ha
      determinantFactor := by
        rw [H.polynomialSchurSeries.alignLeft_determinant,
          H.polynomialSchurSeries_determinant, hd]
        exact (mul_assoc _ _ _).symm
    }
    have hz : S.series.offDiag.coeff D = 0 ∧ S.series.kernel.coeff D = 0 := by
      apply hb.alignLeft_transverse_coeffs_eq_zero_of_clock_le
        (by omega) hw.1 hw.2 hp D
      dsimp [D]
      rw [Fin.sum_univ_four]
      omega
    have hpre := hbound S rfl hz
    exact ⟨S, rfl, Or.inl ⟨hp, rfl⟩, hpre,
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre⟩
  · let S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K) := {
      series := H.polynomialSchurSeries.alignRight hp
      clearingFactor := H.activeDet
      defect := D
      leading_ne_zero := H.polynomialSchurSeries.alignRight_leading_ne_zero hp
      clearingFactor_coeff_zero_ne_zero := ha
      determinantFactor := by
        rw [H.polynomialSchurSeries.alignRight_determinant,
          H.polynomialSchurSeries_determinant, hd]
    }
    have hz0 := R.pr_raySchur_coeffs_eq_zero_of_clock_le hthree hout D (le_refl D)
    have hz : S.series.offDiag.coeff D = 0 ∧ S.series.kernel.coeff D = 0 :=
      ⟨hz0.2.1, hz0.1⟩
    have hpre := hbound S rfl hz
    exact ⟨S, rfl, Or.inr ⟨hp, rfl⟩, hpre,
      S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre⟩

/-- At the first preterminal ray-Schur order the aligned binary coefficient
block is already nondegenerate.  This is a statement only about the honest
reverse-Rees family built from the terminal source; it does not identify that
auxiliary clock with the zero-defect blocker and asserts no global progress.

The key point is that exact-clock algebra kills the kernel coefficient below
closure while the off-diagonal coefficient is nonzero.  Hence the determinant
of the coefficient block is the literal negative square `-B^2`. -/
theorem QsOtherFacetRayReverseReesPackage.pr_exists_exact_preterminal_nondegenerateSchurCoefficient
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hout : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := permutedFamilyHessianFourBlock qsPrSuperfaceSchurPermutation
      (reverseWeightedReesFamily R.weight R.level
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) R.bound)
    ∃ S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K),
      S.defect = 4 * R.level - 2 * ∑ i : Fin 4, R.weight i ∧
      ((∃ h : H.polynomialSchurSeries.LeftPivot,
          S.series = H.polynomialSchurSeries.alignLeft h) ∨
        (∃ h : H.polynomialSchurSeries.RightAxisPivot,
          S.series = H.polynomialSchurSeries.alignRight h)) ∧
      S.firstOrder < S.defect ∧
      S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
      S.series.kernel.coeff S.firstOrder = 0 ∧
      S.series.active.coeff S.firstOrder *
          S.series.kernel.coeff S.firstOrder -
        S.series.offDiag.coeff S.firstOrder *
          S.series.offDiag.coeff S.firstOrder ≠ 0 := by
  rcases R.pr_exists_exact_preterminal_schurClock hthree hout with
    ⟨S, hdef, halign, hpre, hoff⟩
  have hkernel : S.series.kernel.coeff S.firstOrder = 0 :=
    S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre
  refine ⟨S, hdef, halign, hpre, hoff, hkernel, ?_⟩
  rw [hkernel]
  simp only [mul_zero, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero hoff hoff)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
