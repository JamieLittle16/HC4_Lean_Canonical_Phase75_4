import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamData
import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgameProvenance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRightRecenteredKernelExit
import Mathlib.Tactic

/-!
# G1: right-recentered determinant-one final seam

The final zero-strict-low seam is most useful after translating the retained
right collision point to the source origin.  All ingredients needed for that
normalization are already green:

* the honest endpoint-family translation preserves the exact Hessian clock;
* its special fibre is literally the longitudinal right recentering of the
  represented special fibre;
* the exact moving collision becomes zero versus negative e0;
* the two special points remain distinct; and
* the retained zero source jet implies that every source-linear coefficient
  of the right-recentered special fibre vanishes.

At zero clock the translated special fibre therefore still has Hessian
determinant exactly one.  This file only packages those facts beside the
existing exact mixed-degree / first-departure / first-contact data.

No progress theorem, repair transition, terminal cocharacter, source-complexity
interpretation, or JC2 hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- G1 canonical right-recentered local problem.

The fibre is the honest represented special fibre translated by the marked
right endpoint.  It is again determinant one, has zero linear source jet at
the new origin, and retains a distinct exact collision with the negative
marked longitudinal axis.  The exact Smith fibre data and first-contact
Hessian geometry are carried on this same polynomial. -/
structure FinalSeamRightRecenteredData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop where
  hessianDeterminant_one :
    HC4.Polynomial.hessianDeterminant T.rightRecenteredSpecialFiber = 1
  exactCollision :
    HasExactGradientCollision
      T.rightRecenteredSpecialFiber
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  collisionPoints_ne :
    (fun _ : Fin 4 => (0 : K)) ≠
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i)
  linearCoeff_zero :
    ∀ i : Fin 4,
      MvPolynomial.coeff (Finsupp.single i 1)
        T.rightRecenteredSpecialFiber = 0
  mixedDegree :
    ExactSmithExponentMixedDegreeData
      T.rightRecenteredSpecialFiber T.terminal.exponent
  firstDeparture :
    HasFirstExactSmithExponentLongitudinalDeparture
      T.rightRecenteredSpecialFiber T.terminal.exponent
  firstContact :
    AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
      T.rightRecenteredSpecialFiber (0 : Fin 4)

/-- The right-recentered special fibre still has Hessian determinant exactly
one.  This is proved through the honest translated polynomial family, not by
postulating affine covariance directly on the special fibre. -/
theorem rightRecenteredSpecialFiber_hessianDeterminant_eq_one
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Polynomial.hessianDeterminant T.rightRecenteredSpecialFiber = 1 := by
  let E := T.terminal.blocker.blocker.aligned.endpoint
  have hdef := E.rightRecenteredFamily_hessianDefect
  unfold HasPolynomialFamilyHessianDefect at hdef
  have hspecial :=
    hessianDeterminant_polynomialFamilySpecialFiber E.rightRecenteredFamily
  rw [E.rightRecenteredFamily_specialFiber] at hspecial
  rw [hdef, T.zeroClockFirstContactPacket.2.1] at hspecial
  simp at hspecial
  simpa [rightRecenteredSpecialFiber, representedSpecialFiber,
    E, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
    T.terminal.blocker.family_eq] using hspecial

/-- The honest recentered collision specializes to zero versus negative e0 on
the same right-recentered determinant-one fibre. -/
theorem rightRecenteredSpecialFiber_exactAxisCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasExactGradientCollision
      T.rightRecenteredSpecialFiber
      (fun _ : Fin 4 => (0 : K))
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  let E := T.terminal.blocker.blocker.aligned.endpoint
  have h := E.rightRecenteredSpecialFiber_exactCollision
  rw [E.rightRecenteredFamily_specialFiber,
    E.rightRecenteredRightSection_specialPoint] at h
  simpa [rightRecenteredSpecialFiber, representedSpecialFiber,
    E, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
    T.terminal.blocker.family_eq] using h

/-- The translated collision is still genuinely nontrivial. -/
theorem rightRecenteredSpecialFiber_collisionPoints_ne
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (fun _ : Fin 4 => (0 : K)) ≠
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  let E := T.terminal.blocker.blocker.aligned.endpoint
  have h := E.rightRecenteredSpecialPoints_ne
  rw [E.rightRecenteredRightSection_specialPoint] at h
  simpa using h

/-- The translated marked endpoint is a zero-jet source origin: every linear
coefficient vanishes on the same determinant-one special fibre. -/
theorem rightRecenteredSpecialFiber_linearCoeff_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1)
      T.rightRecenteredSpecialFiber = 0 := by
  let E := T.terminal.blocker.blocker.aligned.endpoint
  have h :=
    T.terminal.blocker.blocker.rightRecenteredSpecialFiber_linearCoeff_zero i
  rw [E.rightRecenteredFamily_specialFiber] at h
  simpa [rightRecenteredSpecialFiber, representedSpecialFiber,
    E, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
    T.terminal.blocker.family_eq] using h

/-- Assemble G1 entirely from already-certified data. -/
theorem finalSeamRightRecenteredData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalSeamRightRecenteredData := by
  have S := T.finalSeamData
  exact {
    hessianDeterminant_one :=
      T.rightRecenteredSpecialFiber_hessianDeterminant_eq_one
    exactCollision := T.rightRecenteredSpecialFiber_exactAxisCollision
    collisionPoints_ne := T.rightRecenteredSpecialFiber_collisionPoints_ne
    linearCoeff_zero := T.rightRecenteredSpecialFiber_linearCoeff_zero
    mixedDegree := S.mixedDegree
    firstDeparture := S.firstDeparture
    firstContact := S.firstContact
  }

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
