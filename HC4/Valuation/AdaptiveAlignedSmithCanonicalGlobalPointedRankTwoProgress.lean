import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
import Mathlib.Tactic

/-!
# A18.4.1: geometric progress from the actual pointed rank-two presentation

A18.3 turns every zero-Schur rank-two event into an actual scale-aware
pointed-reflection state.  The presentation itself is deliberately not a
recursive edge: it is a pure ramified re-presentation of the incoming state.

The rank-two geometry carried by that presentation does, however, justify the
finite rank-one -> rank-two promotion on the *presented family*.  This file
packages the composite

    source
      -- honest pointed ramified presentation --> pointed
      -- geometry-justified rank-two promotion --> target

as one globally well-founded edge.  The numerical decrease is the existing
finite repair measure, but unlike the old bookkeeping-only macro the complete
A18.2/A18.3 geometry is retained in the edge certificate.

This is intentionally the only new recursive edge introduced here.  The
legacy rank-two macro and bare internal-presentation branch remain quarantined
for the next A18.4 assembly step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A globally strict rank-two macro whose rank promotion is attached to the
actual A18.3 pointed-family presentation.

The `presentation` field is the soundness payload: downstream recursion never
receives a naked `withRepairOnly` step.  `presentedProgress` records the local
same-scale promotion on the actual pointed state, while `globalProgress`
records the strict finite macro-key decrease from the original source. -/
structure AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presentation :
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
      RR s complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target =
      presentation.geometry.pointedReflectionState.withRepairOnly
        (rankTwoRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target
      presentation.geometry.pointedReflectionState
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- The target of the pointed rank-two macro retains the actual pointed
family.  This is the elementary regression fact distinguishing the composite
from a repair-only relabel of the incoming state. -/
@[simp]
theorem AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress.target_family
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR s complexity) :
    D.target.family = D.presentation.geometry.pointedReflectionState.family := by
  rw [D.target_eq]
  rfl

/-- The target also sits at the literal scale of the honest pointed
presentation, rather than silently returning to the incoming scale. -/
@[simp]
theorem AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress.target_scale
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR s complexity) :
    D.target.scale = alignedSmithRamificationIndex * s.scale := by
  rw [D.target_eq]
  exact D.presentation.geometry.pointedReflectionState_scale

/-- **A18.4.1 pointed rank-two geometric macro.**

Promote the repair rank only after moving to the actual A18.3 pointed family.
The local promotion is same-scale relative to that presented state.  Globally,
the composite is strict because the rank-one -> rank-two repair measure drops,
and the A18.3 geometry remains part of the certificate witnessing why this
particular promotion is legitimate. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation.toGlobalProgress
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoPresentation
      RR s complexity)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR s complexity := by
  let pointed := P.geometry.pointedReflectionState
  let target := pointed.withRepairOnly (rankTwoRepairState complexity)

  have hrepairPointed :
      pointed.repair = rankOneRepairState complexity := by
    simpa [pointed] using P.geometry.pointedReflectionState_repair.trans hsrepair

  have hrepair :
      RepairProgress pointed.repair (rankTwoRepairState complexity) := by
    simpa [hrepairPointed] using
      rankOne_to_rankTwo_repairProgress complexity

  have hpresented :
      CertifiedSameScaleEpisodeProgress RR target pointed := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target,
        ScaleAwareAdaptiveGeometricRestartState.withRepairOnly] using hrepair

  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    simpa [target, pointed,
        ScaleAwareAdaptiveGeometricRestartState.withRepairOnly, hsrepair] using
      repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    presentation := P
    target := target
    target_eq := rfl
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-- A18.4 frontier after consuming the new A18.3 zero-Schur branch.

The legacy macro and bare ramified presentation are deliberately still present:
neither is accepted as recursive progress by this theorem.  The important
change is that `zeroSchurPointedRankTwo` has disappeared and is replaced by a
strict, geometry-carrying global successor. -/
inductive AdaptiveAlignedSmithCanonicalGlobalPointedProgressOutcome
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

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
          RR s complexity))

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.4.1 global pointed-progress frontier.**

Consume the actual-family zero-Schur pointed presentation immediately.  No
legacy macro or generic internal presentation is converted to progress here. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalPointedProgressFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPointedProgressOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalPointedRankTwoFrontier
      RR complexity hsrepair with
  | zeroDefectReentry D =>
      exact .zeroDefectReentry D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | legacyRankTwoMacro outer target hmove hprogress =>
      exact .legacyRankTwoMacro outer target hmove hprogress
  | zeroSchurPointedRankTwo hP =>
      rcases hP with ⟨P⟩
      exact .pointedRankTwoProgress ⟨P.toGlobalProgress hsrepair⟩
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
