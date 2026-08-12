import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import HC4.Valuation.AdaptiveAlignedSmithExactFourBlockSchur
import HC4.Valuation.RigidPacketZeroSchurBridge
import Mathlib.Tactic

/-!
# Closed local endgame for a canonical aligned-Smith blocker

The blocker geometry is now exhausted.

At positive Hessian defect the honest right-recentered Hessian four-block
splits into an exact rank-one Schur chart, an exact zero-Schur chart, or the
all-minors branch.  The all-minors branch is itself exhausted by the recent
finite-support argument:

* a transverse-linear term forces a quadratic persistent packet;
* higher transverse support without a linear term is impossible;
* complete transverse freeness gives the generic saturated-kernel fixed-scale
  strict restart.

Thus no opaque blocker constructor remains.  The only outputs are objects
already understood elsewhere in the repository: strict fixed-scale progress,
strict rank-one -> rank-two repair, exact closing Schur data, or a rigid
persistent packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- A pure-longitudinal transverse-free blocker already contains an honest
certified strict fixed-scale successor.  This wrapper hides only the canonical
denominator-clearing ramification chosen by the generic kernel-free theorem. -/
def HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap) : Prop :=
  let a := B.aligned.toAdaptiveState s
  let R :=
    kernelSlopeDenominatorClearingRamification
      (3 : Fin 4) a.family
  ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
    CertifiedFixedScaleEpisodeProgress RR target
      (a.parameterRamifiedScaleAwareState R
        (kernelSlopeDenominatorClearingRamification_pos
          (3 : Fin 4) a.family))

/-- Transverse freeness of the pure blocker gives the packaged strict
successor immediately. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.certifiedStrictSuccessor_of_transverseFree
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (hfree :
      ∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
        d (1 : Fin 4) = 0 ∧
        d (2 : Fin 4) = 0 ∧
        d (3 : Fin 4) = 0) :
    HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor RR B := by
  unfold HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor
  dsimp only
  rcases
      B.exists_certifiedFixedScaleStrictSuccessor_of_rawSpecialFiber_free_three
        RR (fun d hd => (hfree d hd).2.2) with
    ⟨target, hprogress, _hactive⟩
  exact ⟨target, hprogress⟩

/-- The closing alternative produced by an exact rank-one Schur clock on the
actual blocker family. -/
def HasAdaptiveAlignedSmithBlockerSchurClosing
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop :=
  ∃ S : AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint,
    S.firstOrder = B.aligned.endpoint.defect ∧
      (S.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
       S.series.kernel.coeff B.aligned.endpoint.defect ≠ 0)

/-- The closing alternative of an exact zero-Schur four-block over the
MvPolynomial coefficient domain.  This is exactly the second output of
`ExactZeroSchurFourBlockData.rankTwoProgress_or_closing`. -/
def HasAdaptiveAlignedZeroSchurClosing
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) : Prop :=
  (Z.toClock.residualDefect = 0 ∧
    Z.toClock.tailSeries.active.coeff 0 *
        Z.toClock.tailSeries.kernel.coeff 0 -
      Z.toClock.tailSeries.offDiag.coeff 0 *
        Z.toClock.tailSeries.offDiag.coeff 0 ≠ 0) ∨
  (∃ S : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K),
    0 < Z.toClock.residualDefect ∧
    S.defect = Z.toClock.residualDefect ∧
    S.firstOrder = S.defect ∧
    (S.series.offDiag.coeff S.defect ≠ 0 ∨
     S.series.kernel.coeff S.defect ≠ 0))

/-- **Closed local blocker outcome.**

There is deliberately no constructor for an unresolved blocker geometry. -/
inductive AdaptiveAlignedSmithBlockerEndgameOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ) : Prop

  | certifiedStrictSuccessor
      (h : HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor RR B)

  | rankTwoRepair
      (h : RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity))

  | schurClosing
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | zeroSchurClosing
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | planarRigidPacket
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- A planar quadratic packet is already either rigid or strict rank-two
repair progress. -/
theorem AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint.toBlockerEndgame
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .planarRigidPacket P hrigid
  · exact .rankTwoRepair hprogress

/-- The one-monomial `w^2` packet is likewise already rigid or strict
rank-two repair progress. -/
theorem AdaptiveAlignedSmithWSquarePacketEndpoint.toBlockerEndgame
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .wSquareRigidPacket P hrigid
  · exact .rankTwoRepair hprogress

/-- **Canonical blocker geometry is closed at positive defect.**

Every positive-defect canonical blocker is reduced to an already-established
strict-progress, closing, or rigid-packet interface.  In particular there is
no residual pure-longitudinal/higher-support branch. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.endgame
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity := by
  rcases B.rightRecenteredHessianFrontier_with_allMinors hdefect with
    hschur | hzero | hres

  · rcases
        B.rankTwoProgress_or_closing_of_exactFourBlock
          (complexity := complexity) hschur with
      hprogress | hclosing
    · rcases hprogress with ⟨_S, hrepair, _hoffdiag, _hmeasure⟩
      exact .rankTwoRepair hrepair
    · exact .schurClosing hclosing

  · rcases hzero with ⟨Z⟩
    rcases Z.rankTwoProgress_or_closing complexity with
      hprogress | hclosing
    · exact .rankTwoRepair hprogress
    · exact .zeroSchurClosing Z hclosing

  · have hall := hres.2
    rcases B.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases
          B.pureLongitudinal_transverseFree_or_quadraticPacket
            hpure hall with
        hfree | hplanar' | hw'
      · exact .certifiedStrictSuccessor
          (B.certifiedStrictSuccessor_of_transverseFree RR hfree)
      · rcases hplanar' with ⟨P⟩
        exact P.toBlockerEndgame RR complexity
      · rcases hw' with ⟨P⟩
        exact P.toBlockerEndgame RR complexity

    · rcases hplanar with ⟨P⟩
      exact P.toBlockerEndgame RR complexity

    · rcases hw with ⟨P⟩
      exact P.toBlockerEndgame RR complexity

end

end HC4.Valuation
