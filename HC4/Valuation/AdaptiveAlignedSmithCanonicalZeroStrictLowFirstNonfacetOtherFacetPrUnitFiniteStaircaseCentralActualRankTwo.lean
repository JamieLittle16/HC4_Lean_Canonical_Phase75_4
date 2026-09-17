import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCentralRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit
import Mathlib.Tactic

/-!
# Lift central unit finite-staircase rank-two geometry to the actual state

The unit central branch already exposes a nonzero `(0,3)` Hessian principal
minor on an exact coordinate-max initial face of the source-honest planar
carrier.  The generic initial-form transport lifts that nonvanishing first to
the whole planar carrier and then to the represented presented special fibre.
The existing active-determinant constant-coefficient identity then packages it
as the actual rank-two Hessian chart consumed by the parent `.pr` assembly.
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

/-- A central unit source monomial gives an actual rank-two Hessian chart on
`T.terminal.blocker.presented`. -/
noncomputable def QsOtherFacetPrUnitLeftContactFrontierData.central_actualRankTwoHessianChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {c : Fin 4 →₀ ℕ}
    (hc : c ∈ P.carrier.support)
    (hc1 : c 1 = 0)
    (hc2 : c 2 = 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let hcentral := F.central_coordinateMax_face_rankTwo
      hthree houtThree hc hc1 hc2
  let D := Classical.choose hcentral
  have hspec := Classical.choose_spec hcentral
  have hminor :
      HC4.Polynomial.hessianPrincipalMinor
        D.face (0 : Fin 4) (3 : Fin 4) ≠ 0 :=
    hspec.2.2.2

  have hcarrier :
      HC4.Polynomial.hessianPrincipalMinor
        P.carrier (0 : Fin 4) (3 : Fin 4) ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D.weight_bound (0 : Fin 4) (3 : Fin 4)
    rw [← D.face_eq]
    exact hminor

  have hpresented :
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (0 : Fin 4) (3 : Fin 4) ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      P.source_bound (0 : Fin 4) (3 : Fin 4)
    rw [← P.carrier_eq_initialForm]
    exact hcarrier

  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using hpresented

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
