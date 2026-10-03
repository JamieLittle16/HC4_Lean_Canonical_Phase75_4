import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.3: flatten the terminal rank-three geometry into primitive cases

The normalized presented terminal of A18.5.1 still contains several layers of
historical wrappers.  Before proving the terminal source/exponent-line splice,
we want a finite case split whose constructors are exactly the genuinely
retained geometric events.

This file performs only that lossless flattening.  It exposes nine cases:

* zero-defect blocker geometry;
* blocker kernel-opening geometry;
* blocker preterminal Schur nondegeneracy;
* blocker exact zero-Schur geometry;
* blocker stationary residual chart geometry;
* zero-defect surviving geometry;
* surviving kernel-opening geometry;
* surviving rigid-exposure scalar zero-Schur geometry;
* surviving packet-family rank-three geometry.

There is no boundary constructor: A18.5.1 already absorbed it into a presented
blocker or surviving endpoint.  There is no `RepairProgress` constructor and no
new mathematical assertion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Primitive geometric alternatives underlying every terminal produced by
A18.4.109.  Each constructor retains the endpoint object required to relate
its local chart/packet back to the actual presented polynomial family. -/
inductive AdaptiveAlignedSmithCanonicalPrimitiveRankThreeTerminal
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | blockerZeroDefect
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity)
  | blockerKernel
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity)
  | blockerSchurPreterminal
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (hpre : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)
      (geometry : AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
        chart.clock hpre complexity)
  | blockerZeroSchur
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        chart.zeroData complexity)
  | blockerResidual
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker
        D.presented)
      (geometry : AdaptiveAlignedSmithCanonicalResidualRankThreeGeometry
        stationary complexity)
  | survivingZeroDefect
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
        source complexity)
  | survivingKernel
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity)
  | survivingRigidExposure
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) D.presented W P)
      (hD : 3 ≤ P.degree)
      (Q : AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
        RR D.presented W P R hD complexity)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
        Q.geometry.zeroSchur complexity)
  | survivingPacketFamily
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) D.presented W P complexity)
      (geometry : AdaptiveAlignedSmithCanonicalPacketRankThreeProgress
        D.presented W P complexity R2 hD)

/-- **Lossless primitive terminal split.**
Every normalized terminal is one of the nine concrete geometric cases above. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.toPrimitive
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalPrimitiveRankThreeTerminal
      RR source complexity := by
  cases T with
  | blocker D geometry =>
      cases geometry with
      | zero G =>
          exact .blockerZeroDefect D G
      | positive G =>
          cases G with
          | kernel G =>
              exact .blockerKernel D G
          | schurPreterminal chart hpre G =>
              exact .blockerSchurPreterminal D chart hpre G
          | zeroSchur chart G =>
              exact .blockerZeroSchur D chart G
          | residual S G =>
              exact .blockerResidual D S G
  | surviving D geometry =>
      cases geometry with
      | zero G =>
          exact .survivingZeroDefect D G
      | kernel G =>
          exact .survivingKernel D G
      | existing G =>
          cases G with
          | rigidExposure W P R hD Q G =>
              exact .survivingRigidExposure D W P R hD Q G
          | packetFamily W P hD R2 G =>
              exact .survivingPacketFamily D W P hD R2 G

/-- Primitive terminal geometry attached directly to the final state of the
well-founded rank-one trace. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedPrimitiveRankThree
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalPrimitiveRankThreeTerminal
      RR T.reachedPresentedRankThree.state complexity :=
  T.reachedPresentedRankThree.terminal.toPrimitive

end

end HC4.Valuation
