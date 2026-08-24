import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPreFinalFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalUniformRamification

/-!
# Final assembly A17.6: ramified-spend macro closure

The local-free A17.4 frontier still exposes a `CertifiedRamifiedRawDefectSpend`
as a bare cross-scale exit.  Such a certificate already contains enough
bookkeeping to split the transition canonically into two pieces:

1. pure parameter ramification of the incoming state by the recorded factor;
2. a literal same-scale strict raw-defect drop from that ramified presentation
   to the spend target.

This file records that factorisation and uses it to remove the bare
`ramifiedSpend` constructor from the stationary planar-core frontier.

This is an interface theorem, not a claim that arbitrary chains of changing
ramification scales are well founded.  The zero-cost presentation is retained
explicitly in the macro certificate so the final global assembly cannot hide
that issue.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithBlockerClockProvenance

/-- Every certified ramified spend factors through the literal pure
ramification of its source, followed by an honest same-scale strict
raw-defect step.

The intermediate state is not guessed: it is exactly
`source.parameterRamifiedState h.ramification`. -/
theorem HasCertifiedRamifiedRawDefectSpend.exists_internal_then_sameScaleProgress
    (RR : RepairRanking)
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hspend : HasCertifiedRamifiedRawDefectSpend target source) :
    ∃ outer : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedEpisodeInternalMove outer source ∧
      CertifiedSameScaleEpisodeProgress RR target outer := by
  change Nonempty (CertifiedRamifiedRawDefectSpend target source) at hspend
  rcases hspend with ⟨hcert⟩
  let outer := source.parameterRamifiedState
    hcert.ramification hcert.ramification_pos

  have hmove : HasCertifiedRamifiedEpisodeInternalMove outer source := by
    change Nonempty (CertifiedRamifiedEpisodeInternalMove outer source)
    exact ⟨{
      ramification := hcert.ramification
      ramification_pos := hcert.ramification_pos
      scale_eq := by rfl
      raw_eq := by rfl
      degreeCap_eq := by rfl
      sourceComplexity_eq := by rfl
      repair_eq := by rfl
    }⟩

  have hsame : SameEpisodeScale target outer := by
    unfold SameEpisodeScale
    rw [hcert.scale_eq]
    rfl

  have hraw : target.rawDefect < outer.rawDefect := by
    simpa [outer] using hcert.raw_lt

  exact ⟨outer, hmove,
    certifiedSameScaleEpisodeProgress_of_rawDefect_lt RR hsame hraw⟩

end AdaptiveAlignedSmithBlockerClockProvenance

/-- The stationary planar-core frontier after every strict exit has been put
in one uniform macro form.

There is no bare ramified-spend constructor and no residual local geometry.
`internalPresentation` remains visibly zero-cost and therefore is not
mislabelled as recursive progress. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreMacroClosedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : s.rawDefect = 0)
  | strictMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.6 macro-closed preassembly frontier.**

A17.4 has already removed all local geometry.  The only additional work here
is bookkeeping: a ramified spend is factored through its canonical pure
ramification presentation, while the existing rank-two macro is already in
that form. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreMacroClosedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreMacroClosedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePreFinalAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      rcases hspend.exists_internal_then_sameScaleProgress RR with
        ⟨outer, hmove, hprogress⟩
      exact .strictMacro outer target hmove hprogress
  | rankTwoMacro outer target hmove hprogress =>
      exact .strictMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
