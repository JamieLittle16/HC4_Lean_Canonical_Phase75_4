import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
import Mathlib.Tactic

/-!
# A18.4.2: quarantine the legacy rank-two macro at its honest outer state

A18.4.1 consumed the new zero-Schur pointed rank-two branch by attaching the
rank promotion to an actual family-changing pointed presentation.  One older
`rankTwoMacro` branch still survives from the pre-A18 exact-clock assembly.
Its interface stores

    source -- pure ramified presentation --> outer
           -- same-scale progress -------> target.

The first arrow is honest and data-bearing.  The second arrow is too weak for
final global recursion: in the legacy producer it may be only
`withRepairOnly (rankTwoRepairState complexity)`.

The sound replacement is therefore not to recurse to `target` and not to
attempt to reconstruct geometry which the old interface has already erased.
We discard the legacy target and retain only `outer` as an internal
presentation.  Since a certified ramified internal move preserves the repair
state, the canonical rank-one classifier may later be rerun on `outer` with
exactly the same repair hypothesis.

After this file there is no legacy rank-two constructor in the exported global
frontier.  The only unresolved non-strict branch is the uniform
`internalPresentation` branch, which A18.4.3 can consume separately.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A propositional certified ramified presentation preserves the finite
repair state.  This small adapter is the key fact needed to rerun the rank-one
global classifier on a quarantined presentation state. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.repair_eq
    {s t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : HasCertifiedRamifiedEpisodeInternalMove t s) :
    t.repair = s.repair := by
  change Nonempty (CertifiedRamifiedEpisodeInternalMove t s) at hmove
  rcases hmove with ⟨h⟩
  exact h.repair_eq

/-- Hence an honest internal presentation of a canonical rank-one state is
itself canonical rank one with the same complexity. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.rankOne_repair_eq
    {s t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (hmove : HasCertifiedRamifiedEpisodeInternalMove t s)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    t.repair = rankOneRepairState complexity := by
  exact hmove.repair_eq.trans hsrepair

/-- A18.4 frontier with the old rank-two macro removed.

`pointedRankTwoProgress` is the geometry-carrying strict successor introduced
in A18.4.1.  Every older rank-two macro is now represented only by its honest
ramified outer state under `internalPresentation`; its potentially
bookkeeping-only target is intentionally absent from this type. -/
inductive AdaptiveAlignedSmithCanonicalGlobalLegacyQuarantineOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
          RR s complexity))

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.4.2 legacy quarantine theorem.**

Consume A18.4.1 and erase the unsafe part of every legacy rank-two macro.  In
that case the old same-scale target/progress proof is deliberately ignored:
only the certified ramified `outer` presentation survives.

This is a monotone soundness refinement of the frontier: no new recursive edge
is asserted.  It also gives A18.4.3 a single presentation constructor to deal
with, regardless of whether that presentation originated from the old
rank-two path or from an ordinary internal normalization. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalLegacyQuarantineFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalLegacyQuarantineOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalPointedProgressFrontier
      RR complexity hsrepair with
  | zeroDefectReentry D =>
      exact .zeroDefectReentry D
  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D
  | legacyRankTwoMacro outer target hmove hprogress =>
      -- The legacy `target` and `hprogress` may encode only repair relabeling.
      -- The outer state is the maximal source-honest information in this API.
      -- A18.4.5 now retains the producer as presentation provenance instead of
      -- erasing it completely.
      exact .internalPresentation outer hmove
        (.legacyRankTwo outer target hmove hprogress)
  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
