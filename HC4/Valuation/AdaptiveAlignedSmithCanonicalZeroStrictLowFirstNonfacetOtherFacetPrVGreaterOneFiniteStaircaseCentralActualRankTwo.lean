import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralClosure
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree
import Mathlib.Tactic

/-!
# Lift central finite-staircase rank-two geometry to the actual presented state

The central finite-staircase branch already supplies a nonzero `(0,3)` Hessian
principal minor on an exact coordinate-max initial face of the source-honest
planar carrier.  Two applications of the generic maximal-initial Hessian-minor
transport lift that nonvanishing first to the planar carrier and then to the
actual presented special fibre.

The resulting nonzero special-fibre minor is exactly the constant coefficient
of the active determinant in the corresponding scale-aware Hessian chart.
Thus the central branch produces the existing
`AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart` on the real presented
state, and hence feeds the already-green actual-rank-two to rank-three geometry
consumer with no repair-only relabelling and no auxiliary singular carrier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Constant coefficient of a scale-aware active determinant is exactly the
principal Hessian minor of the honest special fibre in the selected active
coordinates. -/
theorem scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareHessianFourBlock rho s).activeDet.coeff 0 =
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber s.family) (rho 0) (rho 1) := by
  have hsym :
      HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber s.family) (rho 0) (rho 1) =
        HC4.Polynomial.hessian
          (polynomialFamilySpecialFiber s.family) (rho 1) (rho 0) := by
    change
      MvPolynomial.pderiv (rho 1)
          (MvPolynomial.pderiv (rho 0)
            (polynomialFamilySpecialFiber s.family)) =
        MvPolynomial.pderiv (rho 0)
          (MvPolynomial.pderiv (rho 1)
            (polynomialFamilySpecialFiber s.family))
    exact pderiv_comm_commRing (rho 1) (rho 0)
      (polynomialFamilySpecialFiber s.family)
  unfold scaleAwareHessianFourBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix HC4.Polynomial.hessianPrincipalMinor
  simp only [Matrix.submatrix_apply]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  simp only [← Polynomial.coeff_zero_eq_eval_zero]
  simp_rw [scaleAwareHessianSeriesMatrix_coeff_zero]
  simpa only [hsym]

/-- Any honest nonzero special-fibre principal Hessian minor can be made the
active block of a scale-aware rank-two chart by a finite coordinate
permutation. -/
noncomputable def actualRankTwoHessianChart_of_specialFiber_minor
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {i k : Fin 4}
    (hik : i ≠ k)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber s.family) i k ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s := by
  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) i
  let tau : Equiv.Perm (Fin 4) := Equiv.swap (sigma (1 : Fin 4)) k
  let rho : Equiv.Perm (Fin 4) := sigma.trans tau
  have hs0 : sigma (0 : Fin 4) = i := by
    simp [sigma]
  have hs1_ne_i : sigma (1 : Fin 4) ≠ i := by
    intro h
    have h' : sigma (1 : Fin 4) = sigma (0 : Fin 4) := by
      rw [hs0]
      exact h
    have : (1 : Fin 4) = 0 := sigma.injective h'
    norm_num at this
  have hrho0 : rho (0 : Fin 4) = i := by
    dsimp [rho]
    rw [Equiv.trans_apply, hs0]
    simp [tau, hs1_ne_i, hik]
  have hrho1 : rho (1 : Fin 4) = k := by
    dsimp [rho]
    rw [Equiv.trans_apply]
    simp [tau]
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  rw [hrho0, hrho1]
  exact hminor

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}

/-- The central monomial's nonzero principal minor lifts through its exact
coordinate-max exposure to the whole source-honest planar carrier. -/
theorem carrier_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor
      P.carrier (0 : Fin 4) (3 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    G.exposure.weight_bound (0 : Fin 4) (3 : Fin 4)
  rw [← G.exposure.face_eq]
  exact G.exposure_rankTwo_minor

/-- Lift once more through the planar carrier's honest source exposure.  The
nonzero `(0,3)` minor now lives on the actual represented special fibre. -/
theorem presented_specialFiber_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (0 : Fin 4) (3 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    P.source_bound (0 : Fin 4) (3 : Fin 4)
  rw [← P.carrier_eq_initialForm]
  exact G.carrier_hessianPrincipalMinor_ne_zero

/-- The central finite-staircase branch is therefore an actual rank-two
Hessian chart on the real presented state. -/
noncomputable def actualRankTwoHessianChart
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using G.presented_specialFiber_hessianPrincipalMinor_ne_zero

/-- Feed the retained actual rank-two chart directly into the already-green
rank-two to rank-three geometry theorem. -/
noncomputable def actualRankThreeGeometry
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
      G.actualRankTwoHessianChart 0 :=
  G.actualRankTwoHessianChart.rankThreeGeometry 0

end QsOtherFacetPrLeftVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
