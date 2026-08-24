import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSoundAssemblyFrontier

/-!
# A18.2: global geometry-carrying rank-two frontier

A18.1 deliberately quarantines every branch whose apparent recursive progress
could still be only repair bookkeeping.  The three new zero-Schur exits are
better than that: each is attached to the same source-honest
right-recentered family and exact Hessian chart carried by the A17.3F local
problem.

This file compresses those three exits into one data-bearing global object.
The object retains:

* the complete A17.3F local problem;
* the actual right-recentered polynomial family;
* its exact moving gradient collision;
* its exact Hessian determinant clock;
* the exact chart determinant clock;
* the positive aligned endpoint clock; and
* one of the three concrete A17.13--A17.17 rank-two geometric events.

No successor state is manufactured here.  In particular, the legacy
`rankTwoMacro` is still quarantined: its target may have arisen from
`withRepairOnly`.  The next assembly theorem now has one precise task:
construct an actual family-level continuation from
`AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry`.

This is intentionally stronger than merely grouping constructors.  Downstream
code no longer needs to rediscover that every zero-Schur rank-two event lives
on the same honest family/collision/chart package.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The three concrete zero-Schur rank-two geometries surviving A17.17.

This is data-valued.  In the first two constructors the `Nonempty` wrappers
from the proposition-valued frontier are opened, so the actual evaluation
point/nondegenerate block certificate is retained. -/
inductive AdaptiveAlignedSmithCanonicalZeroSchurRankTwoGeometryWitness
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (complexity : ℕ) : Type (u + 1)

  | preterminal
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
      (exit :
        AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
          RR P complexity D)

  | residualZero
      (exit :
        AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
          P.carrier.chartData.zeroData)

  | projective
      (departure :
        AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
          P.carrier.chartData.zeroData complexity)

/-- One global zero-Schur rank-two event together with the exact A17.3F source
problem which generated it.

The important point is that `problem` is retained as data.  Therefore the
honest family, moving collision, endpoint clock and chart can all be recovered
without existential reconstruction or repair-state relabelling. -/
structure AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) where
  problem :
    AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s
  witness :
    AdaptiveAlignedSmithCanonicalZeroSchurRankTwoGeometryWitness
      RR problem complexity

namespace AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry

/-- The retained geometry is attached to the actual right-recentered
polynomial family, not to an auxiliary binary block or residual clock. -/
theorem family_hessianDefect
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    HasPolynomialFamilyHessianDefect (K := K)
      G.problem.carrier.family
      G.problem.stationary.blocker.aligned.endpoint.defect := by
  exact G.problem.carrier.family_hessianDefect

/-- The exact moving gradient collision is retained on that same family. -/
theorem family_exactCollision
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    HasPolynomialFamilyExactGradientCollision
      G.problem.carrier.family
      (zeroPolynomialSection (K := K))
      G.problem.stationary.blocker.aligned.endpoint.rightRecenteredRightSection := by
  exact G.problem.carrier.family_exactCollision

/-- The zero-Schur chart is still the honest exact determinant chart of the
retained family. -/
theorem chart_determinantCore
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    G.problem.carrier.chartData.chart.block.determinantCore =
      Polynomial.X ^ G.problem.stationary.blocker.aligned.endpoint.defect := by
  exact G.problem.carrier.chart_determinantCore

/-- The aligned endpoint clock is the canonical ramified presentation of the
incoming raw defect. -/
theorem clock_eq
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    G.problem.stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect :=
  G.problem.clock_eq

/-- Every retained zero-Schur rank-two geometry occurs at positive endpoint
defect. -/
theorem clock_pos
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity) :
    0 < G.problem.stationary.blocker.aligned.endpoint.defect :=
  G.problem.clock_pos

/-- Package the A17.13 preterminal nondegenerate exit. -/
def ofPreterminal
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
      RR P complexity)
    (exit :
      AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
        RR P complexity D) :
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity where
  problem := P
  witness := .preterminal D exit

/-- Package the A17.14 residual-zero nondegenerate exit. -/
def ofResidualZero
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (exit :
      AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
        P.carrier.chartData.zeroData) :
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity where
  problem := P
  witness := .residualZero exit

/-- Package the A17.17 source-integrated projective departure. -/
def ofProjective
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
    (D :
      AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
        P.carrier.chartData.zeroData complexity) :
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
      RR s complexity where
  problem := P
  witness := .projective D

end AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry

/-- A18.2 assembly outcome.

Relative to A18.1 the three source-honest zero-Schur constructors have been
compressed into a single data-bearing `zeroSchurRankTwoGeometry` constructor.
The old rank-two macro remains explicitly marked as legacy/quarantined because
its target is not yet certified to be a changed family.

Thus there is now exactly one geometry-carrying rank-two family-realisation
obligation for the next assembly pass. -/
inductive AdaptiveAlignedSmithCanonicalGlobalGeometryCarryingOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | legacyRankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | zeroSchurRankTwoGeometry
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry
          RR s complexity))

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.2 geometry-carrying global frontier.**

All three new zero-Schur exits are now one actual-family object.  No proof in
this theorem uses repair progress to manufacture a successor state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalGeometryCarryingFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalGeometryCarryingOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalSoundAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefectReentry D =>
      exact .zeroDefectReentry D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | rankTwoMacro outer target hmove hprogress =>
      exact .legacyRankTwoMacro outer target hmove hprogress
  | zeroSchurNondegenerateRankTwo P D hexit =>
      rcases hexit with ⟨exit⟩
      exact .zeroSchurRankTwoGeometry
        ⟨AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry.ofPreterminal
          P D exit⟩
  | zeroSchurResidualZeroNondegenerate P D =>
      rcases D with ⟨exit⟩
      exact .zeroSchurRankTwoGeometry
        ⟨AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry.ofResidualZero
          (RR := RR) (complexity := complexity) P exit⟩
  | zeroSchurSourceIntegratedProjectiveDeparture P D =>
      exact .zeroSchurRankTwoGeometry
        ⟨AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoGeometry.ofProjective
          (RR := RR) P D⟩
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end
end HC4.Valuation
