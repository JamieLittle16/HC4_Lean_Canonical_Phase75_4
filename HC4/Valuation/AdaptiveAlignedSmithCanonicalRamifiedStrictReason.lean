import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentationFreeExactClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import Mathlib.Tactic

/-!
# A18.4.40: expose the discrete reason behind a ramified strict macro

A `GlobalRamifiedStrictMacro` is a pure ramified presentation followed by a
strict fixed-scale exit.  The wrapper is sound, but it deliberately hides
which coordinate of the fixed-scale lexicographic key decreased.  Final
global termination must recover that distinction: repair and source
complexity are invariant under the pure ramification and therefore give
honest outer well-founded progress, whereas a raw-defect decrease at the
ramified scale must be handled by the first-contact geometry of A18.4.39.

This file performs exactly that lossless split.  It introduces the two-coordinate
outer key `(repair rank, source complexity)`, proves it well-founded, and
shows that every ramified strict macro either decreases that outer key or is
an actual certified ramified raw-defect spend from the original source.

No scale-changing raw decrease is called global progress here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The genuinely scale-insensitive part of the global termination key. -/
abbrev AdaptiveAlignedSmithCanonicalOuterKey := ℕ × ℕ

/-- Repair rank has priority over source complexity. -/
def AdaptiveAlignedSmithCanonicalOuterKey.Lt :
    AdaptiveAlignedSmithCanonicalOuterKey →
      AdaptiveAlignedSmithCanonicalOuterKey → Prop :=
  Prod.Lex Nat.lt Nat.lt

/-- The scale-insensitive outer key is well-founded. -/
theorem AdaptiveAlignedSmithCanonicalOuterKey.lt_wellFounded :
    WellFounded AdaptiveAlignedSmithCanonicalOuterKey.Lt := by
  exact (Nat.lt_wfRel.wf).prod_lex Nat.lt_wfRel.wf

/-- Outer key of a scale-aware state for a certified repair ranking. -/
def ScaleAwareAdaptiveGeometricRestartState.canonicalOuterKey
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalOuterKey :=
  (RR.rank s.repair, s.sourceComplexity)

/-- A concrete, nondependent view of the nested fixed-scale lexicographic
order.  Isolating this arithmetic split avoids dependent elimination on state
projections in the global reason classifier. -/
theorem FixedScaleEpisodeKey.lt_cases
    {d₁ r₁ c₁ d₂ r₂ c₂ : ℕ}
    (h : FixedScaleEpisodeKey.Lt
      (d₁, (r₁, c₁)) (d₂, (r₂, c₂))) :
    d₁ < d₂ ∨
      (d₁ = d₂ ∧
        (r₁ < r₂ ∨ (r₁ = r₂ ∧ c₁ < c₂))) := by
  cases h with
  | left hraw =>
      exact Or.inl hraw
  | right htail =>
      refine Or.inr ⟨rfl, ?_⟩
      cases htail with
      | left hrepair =>
          exact Or.inl hrepair
      | right hsource =>
          exact Or.inr ⟨rfl, hsource⟩

/-- A ramified strict macro either gives scale-insensitive outer progress or
is genuinely a ramified raw-defect spend.  The latter is intentionally kept
separate for the A18.4.39 first-contact termination argument. -/
inductive AdaptiveAlignedSmithCanonicalRamifiedStrictReason
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | outerProgress
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithCanonicalOuterKey.Lt
        (target.canonicalOuterKey RR) (source.canonicalOuterKey RR))
  | rawSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target source)

/-- **Reason classifier for a ramified strict macro.**

The fixed-scale progress proof is a lexicographic proof on
`(rawDefect, repairRank, sourceComplexity)`.

* raw-defect decrease composes with the pure ramification into an honest
  ramified spend from `source`;
* at equal raw defect, repair-rank decrease survives ramification literally;
* at equal raw defect and repair rank, source-complexity decrease likewise
  survives ramification literally.
-/
theorem AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro.reason
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source) :
    AdaptiveAlignedSmithCanonicalRamifiedStrictReason RR source := by
  cases D with
  | mk outer target hmove hprogress =>
      rcases hmove with ⟨hmove⟩
      have hcases :
          target.rawDefect < outer.rawDefect ∨
            (target.rawDefect = outer.rawDefect ∧
              (RR.rank target.repair < RR.rank outer.repair ∨
                (RR.rank target.repair = RR.rank outer.repair ∧
                  target.sourceComplexity < outer.sourceComplexity))) := by
        apply FixedScaleEpisodeKey.lt_cases
        simpa [FixedScaleEpisodeProgress,
          ScaleAwareAdaptiveGeometricRestartState.fixedScaleEpisodeKey] using
          hprogress.progress
      rcases hcases with hraw | ⟨_hrawEq, hrepair | ⟨hrankEq, hsource⟩⟩
      · have hspend :
            AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
              target source := by
          change Nonempty (CertifiedRamifiedRawDefectSpend target source)
          refine ⟨{
            ramification := hmove.ramification
            ramification_pos := hmove.ramification_pos
            scale_eq := ?_
            raw_lt := ?_
          }⟩
          · calc
              target.scale = outer.scale := hprogress.sameScale
              _ = hmove.ramification * source.scale := hmove.scale_eq
          · calc
              target.rawDefect < outer.rawDefect := hraw
              _ = hmove.ramification * source.rawDefect := hmove.raw_eq
        exact AdaptiveAlignedSmithCanonicalRamifiedStrictReason.rawSpend
          target hspend
      · exact AdaptiveAlignedSmithCanonicalRamifiedStrictReason.outerProgress
          target (by
            unfold AdaptiveAlignedSmithCanonicalOuterKey.Lt
            unfold ScaleAwareAdaptiveGeometricRestartState.canonicalOuterKey
            apply Prod.Lex.left
            calc
              RR.rank target.repair < RR.rank outer.repair := hrepair
              _ = RR.rank source.repair := by rw [hmove.repair_eq])
      · have hrankSource :
            RR.rank target.repair = RR.rank source.repair := by
          calc
            RR.rank target.repair = RR.rank outer.repair := hrankEq
            _ = RR.rank source.repair := by rw [hmove.repair_eq]
        exact AdaptiveAlignedSmithCanonicalRamifiedStrictReason.outerProgress
          target (by
            unfold AdaptiveAlignedSmithCanonicalOuterKey.Lt
            unfold ScaleAwareAdaptiveGeometricRestartState.canonicalOuterKey
            rw [hrankSource]
            apply Prod.Lex.right
            calc
              target.sourceComplexity < outer.sourceComplexity := hsource
              _ = source.sourceComplexity := hmove.sourceComplexity_eq)

end

end HC4.Valuation
