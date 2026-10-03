import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSourceSchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# A19 cyclic other-facet source pivots give actual rank-two charts

A19.129 already lifts the nonzero cyclic Hessian pivots from the locked
rank-three ray to the represented special fibre itself.  Once the minor lives
on that actual special fibre, no finite-staircase transport is needed: the
existing scale-aware Hessian chart identity packages it directly as an
`AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart`.

The three possible other facets use the source minors

* `.pr`: `(2,3)`;
* `.sp`: `(1,3)`;
* `.rq`: `(1,2)`.

This file is only the finite coordinate-permutation adapter.  It introduces no
new clock, repair tag, or auxiliary singularity claim.
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

/-- `.pr`: package the represented-source `(2,3)` minor as the active block. -/
private noncomputable def pr_actualRankTwoChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  have hminor := R.pr_source_hessianPrincipalMinor_ne_zero hthree houtThree
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using hminor

/-- `.sp`: package the represented-source `(1,3)` minor as the active block. -/
private noncomputable def sp_actualRankTwoChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  have hminor := R.sp_source_hessianPrincipalMinor_ne_zero hthree houtThree
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using hminor

/-- `.rq`: package the represented-source `(1,2)` minor as the active block. -/
private noncomputable def rq_actualRankTwoChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  have hminor := R.rq_source_hessianPrincipalMinor_ne_zero hthree houtThree
  let rho : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using hminor

/-- **Complete cyclic other-facet rank-two adapter.**  Any rank-three outside
endpoint on a facet different from `.qs` already supplies an actual rank-two
Hessian chart on the represented state. -/
theorem qs_ray_otherFacet_actualRankTwoHessianChart
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases C.qs_ray_otherFacet_rayReverseRees_package
      hthree hne houtThree with ⟨R⟩
  cases next with
  | pr =>
      exact ⟨pr_actualRankTwoChart R hthree houtThree⟩
  | rq =>
      exact ⟨rq_actualRankTwoChart R hthree houtThree⟩
  | qs =>
      exact (hne rfl).elim
  | sp =>
      exact ⟨sp_actualRankTwoChart R hthree houtThree⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
