import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurNondegenerateRankTwo
import Mathlib.Tactic

/-!
# Final assembly A17.14: split the exact zero-Schur closing branch

A17.13 leaves one opaque constructor:

    HasAdaptiveAlignedZeroSchurClosing Z.

By definition that proposition is already a disjunction of two geometrically
very different situations.  This file exposes that distinction without
losing any data.

* If the residual zero-Schur determinant defect is zero, the constant block
  of the normalised tail has nonzero determinant.  Evaluating that nonzero
  source polynomial at a suitable point produces an honest nondegenerate
  binary Schur block with trivial kernel.

* If positive residual determinant remains, the zero-Schur tail has already
  become an exact rank-one Schur clock and its first transverse order is
  exactly closing.  We retain that entire clock and its nonzero closing
  coefficient.

Thus no undifferentiated `HasAdaptiveAlignedZeroSchurClosing` constructor
survives the exported frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Evaluate the constant block of the normalised zero-Schur tail. -/
noncomputable def zeroSchurClosingTailBlockAt
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point (Z.toClock.tailSeries.active.coeff 0)
  b := MvPolynomial.eval point (Z.toClock.tailSeries.offDiag.coeff 0)
  c := MvPolynomial.eval point (Z.toClock.tailSeries.kernel.coeff 0)

/-- Geometry of the residual-defect-zero closing alternative. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) where
  residualDefect_eq_zero : Z.toClock.residualDefect = 0
  point : Fin 4 → K
  detCore_ne_zero : (zeroSchurClosingTailBlockAt Z point).detCore ≠ 0
  trivialKernel : (zeroSchurClosingTailBlockAt Z point).HasTrivialKernel

/-- The positive-residual closing alternative retains the exact residual
rank-one Schur clock rather than only the existential proposition. -/
structure AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) where
  residualClock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K)
  residualDefect_pos : 0 < Z.toClock.residualDefect
  residualClock_defect_eq : residualClock.defect = Z.toClock.residualDefect
  firstOrder_eq_defect : residualClock.firstOrder = residualClock.defect
  closingCoefficient_ne :
    residualClock.series.offDiag.coeff residualClock.defect ≠ 0 ∨
      residualClock.series.kernel.coeff residualClock.defect ≠ 0

/-- Lossless geometric resolution of `HasAdaptiveAlignedZeroSchurClosing`. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurResolvedClosingOutcome
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) : Prop where
  | residualZeroNondegenerate
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit Z))
  | residualRankOneClosing
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData Z))

/-- Split the old opaque zero-Schur closing proposition into its two exact
geometric alternatives. -/
theorem resolveAdaptiveAlignedZeroSchurClosing
    (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
    (h : HasAdaptiveAlignedZeroSchurClosing Z) :
    AdaptiveAlignedSmithCanonicalZeroSchurResolvedClosingOutcome Z := by
  rcases h with hzero | hrankOne
  · rcases hzero with ⟨hres0, hdetPoly⟩
    let detPoly : MvPolynomial (Fin 4) K :=
      Z.toClock.tailSeries.active.coeff 0 *
          Z.toClock.tailSeries.kernel.coeff 0 -
        Z.toClock.tailSeries.offDiag.coeff 0 *
          Z.toClock.tailSeries.offDiag.coeff 0
    have hdetPoly' : detPoly ≠ 0 := by
      simpa [detPoly] using hdetPoly
    rcases exists_source_eval_ne_zero_of_ne_zero detPoly hdetPoly' with
      ⟨point, hpoint⟩
    let q : BinarySchurBlock K := zeroSchurClosingTailBlockAt Z point
    have hdet : q.detCore ≠ 0 := by
      simpa [q, zeroSchurClosingTailBlockAt, BinarySchurBlock.detCore,
        detPoly] using hpoint
    have htrivial : q.HasTrivialKernel :=
      BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
    exact .residualZeroNondegenerate ⟨{
      residualDefect_eq_zero := hres0
      point := point
      detCore_ne_zero := by simpa [q] using hdet
      trivialKernel := by simpa [q] using htrivial
    }⟩
  · rcases hrankOne with ⟨S, hres, hdef, hclose, hcoeff⟩
    exact .residualRankOneClosing ⟨{
      residualClock := S
      residualDefect_pos := hres
      residualClock_defect_eq := hdef
      firstOrder_eq_defect := hclose
      closingCoefficient_ne := hcoeff
    }⟩

/-- A17.14 frontier: the final opaque zero-Schur closing constructor is split
into either an evaluated nondegenerate tail block or an exact residual
rank-one closing clock. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSchurClosingSplitOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | zeroSchurNondegenerateRankTwo
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
      (hexit : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
          RR P complexity D))
  | zeroSchurResidualZeroNondegenerate
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
          P.carrier.chartData.zeroData))
  | zeroSchurResidualRankOneClosing
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualRankOneClosingData
          P.carrier.chartData.zeroData))
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)

/-- **A17.14 exact closing split.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreZeroSchurClosingSplitFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreZeroSchurClosingSplitOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreNondegenerateRankTwoFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | zeroSchurNondegenerateRankTwo P D hexit =>
      exact .zeroSchurNondegenerateRankTwo P D hexit
  | zeroSchurClosing P hclose =>
      cases resolveAdaptiveAlignedZeroSchurClosing P.carrier.chartData.zeroData hclose with
      | residualZeroNondegenerate D =>
          exact .zeroSchurResidualZeroNondegenerate P D
      | residualRankOneClosing D =>
          exact .zeroSchurResidualRankOneClosing P D
  | internalPresentation target hmove =>
      exact .internalPresentation target hmove

end

end HC4.Valuation
