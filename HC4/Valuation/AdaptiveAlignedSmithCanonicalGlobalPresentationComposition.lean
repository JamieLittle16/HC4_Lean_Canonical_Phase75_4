import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalLegacyRankTwoQuarantine
import Mathlib.Tactic

/-!
# A18.4.3: composition algebra for nonrecursive global presentations

A18.4.2 leaves exactly one non-strict global constructor:
`internalPresentation`.  Such a state change is source-honest, but it changes
absolute parameter scale and therefore must never itself be fed to a
well-founded recursion.

The correct global operation is to absorb one or more pure ramified
presentations into the *next genuine geometric exit*.  This file supplies the
missing algebra for that absorption:

* certified ramified internal moves are reflexive and transitive;
* their propositional wrappers compose without exposing data choices;
* zero raw defect reflects backwards through a positive ramification;
* an honest ramified-strict macro may be prefixed by any finite presentation;
* an A18.4.1 pointed rank-two exit reached after a presentation is promoted to
  a strict global macro from the original source while retaining the entire
  presentation/pointed geometry as data.

No presentation is declared recursive progress here.  In particular, this
file does not use `ScaledDefect.LT` as a termination relation and does not
manufacture a rank promotion from a bare `RepairProgress` certificate.
The next A18.4 closure pass can therefore rerun the classifier on a presented
state and compose the result back to the original source without ever making
an intermediate presentation a recursive edge.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Pure-presentation category laws -/

/-- Identity presentation.  It is useful only as a neutral element when a
uniform data structure wants to retain a presentation chain; it is not
progress. -/
def CertifiedRamifiedEpisodeInternalMove.identity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    CertifiedRamifiedEpisodeInternalMove s s where
  ramification := 1
  ramification_pos := by omega
  scale_eq := by simp
  raw_eq := by simp
  degreeCap_eq := rfl
  sourceComplexity_eq := rfl
  repair_eq := rfl

/-- Two consecutive pure ramified presentations compose to one pure ramified
presentation at the product ramification factor. -/
def CertifiedRamifiedEpisodeInternalMove.trans
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsu : CertifiedRamifiedEpisodeInternalMove u s)
    (hut : CertifiedRamifiedEpisodeInternalMove t u) :
    CertifiedRamifiedEpisodeInternalMove t s where
  ramification := hut.ramification * hsu.ramification
  ramification_pos :=
    Nat.mul_pos hut.ramification_pos hsu.ramification_pos
  scale_eq := by
    calc
      t.scale = hut.ramification * u.scale := hut.scale_eq
      _ = hut.ramification * (hsu.ramification * s.scale) := by
        rw [hsu.scale_eq]
      _ = (hut.ramification * hsu.ramification) * s.scale := by
        ac_rfl
  raw_eq := by
    calc
      t.rawDefect = hut.ramification * u.rawDefect := hut.raw_eq
      _ = hut.ramification * (hsu.ramification * s.rawDefect) := by
        rw [hsu.raw_eq]
      _ = (hut.ramification * hsu.ramification) * s.rawDefect := by
        ac_rfl
  degreeCap_eq := hut.degreeCap_eq.trans hsu.degreeCap_eq
  sourceComplexity_eq :=
    hut.sourceComplexity_eq.trans hsu.sourceComplexity_eq
  repair_eq := hut.repair_eq.trans hsu.repair_eq

/-- Propositional identity presentation. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.identity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    HasCertifiedRamifiedEpisodeInternalMove s s := by
  exact ⟨CertifiedRamifiedEpisodeInternalMove.identity s⟩

/-- Propositional transitivity of pure ramified presentations. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.trans
    {s u t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsu : HasCertifiedRamifiedEpisodeInternalMove u s)
    (hut : HasCertifiedRamifiedEpisodeInternalMove t u) :
    HasCertifiedRamifiedEpisodeInternalMove t s := by
  change Nonempty (CertifiedRamifiedEpisodeInternalMove u s) at hsu
  change Nonempty (CertifiedRamifiedEpisodeInternalMove t u) at hut
  change Nonempty (CertifiedRamifiedEpisodeInternalMove t s)
  rcases hsu with ⟨hsu⟩
  rcases hut with ⟨hut⟩
  exact ⟨hsu.trans hut⟩

/-- Pure ramification cannot create a zero raw clock from a positive source
clock.  This is the backwards form needed when a classifier reaches its
zero-defect branch only after an internal presentation. -/
theorem CertifiedRamifiedEpisodeInternalMove.source_rawDefect_eq_zero_of_target
    {s t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : CertifiedRamifiedEpisodeInternalMove t s)
    (htzero : t.rawDefect = 0) :
    s.rawDefect = 0 := by
  by_contra hs
  have hspos : 0 < s.rawDefect := Nat.pos_of_ne_zero hs
  have htpos : 0 < t.rawDefect := by
    rw [hmove.raw_eq]
    exact Nat.mul_pos hmove.ramification_pos hspos
  omega

/-- Propositional wrapper of zero-clock reflection. -/
theorem HasCertifiedRamifiedEpisodeInternalMove.source_rawDefect_eq_zero_of_target
    {s t : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hmove : HasCertifiedRamifiedEpisodeInternalMove t s)
    (htzero : t.rawDefect = 0) :
    s.rawDefect = 0 := by
  change Nonempty (CertifiedRamifiedEpisodeInternalMove t s) at hmove
  rcases hmove with ⟨hmove⟩
  exact hmove.source_rawDefect_eq_zero_of_target htzero

/-! ## Absorbing a presentation into a genuine strict exit -/

/-- Prefixing an already sound ramified-strict macro by a pure presentation
preserves soundness.  The two presentation factors are composed; the genuine
same-scale exit remains exactly the original exit on the final outer state. -/
theorem AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro.prepend_internal
    (RR : RepairRanking)
    {s presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented s)
    (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR presented) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s := by
  cases D with
  | mk outer target houter hprogress =>
      exact .mk outer target (hsource.trans houter) hprogress

/-- A pointed rank-two exit reached after a pure presentation, retaining both
pieces of geometry.

The recursive target is the target of the A18.4.1 pointed macro.  Its strict
comparison is made directly with the original source.  This is legitimate
because the source presentation preserves repair state and the pointed macro
performs the geometry-justified rank-one -> rank-two promotion. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove presented s
  pointedProgress :
    AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR presented complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      pointedProgress.target s

namespace AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress

/-- A direct A18.4.1 pointed exit is the degenerate case with the identity
presentation. -/
noncomputable def ofDirect
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR s complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
      RR s complexity where
  presented := s
  sourcePresentation :=
    HasCertifiedRamifiedEpisodeInternalMove.identity s
  pointedProgress := D
  globalProgress := D.globalProgress

/-- Absorb one pure presentation before an A18.4.1 pointed rank-two exit.

No comparison of raw clocks across scales is used.  Strictness comes entirely
from the rank-one -> rank-two repair decrease already justified by the actual
pointed family carried in `D`; the prefix presentation preserves the source
repair state exactly. -/
noncomputable def ofInternal
    {RR : RepairRanking}
    {s presented : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (hsource : HasCertifiedRamifiedEpisodeInternalMove presented s)
    (D : AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
      RR presented complexity)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
      RR s complexity := by
  have htargetRepair :
      D.target.repair = rankTwoRepairState complexity := by
    rw [D.target_eq]
    rfl

  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress D.target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [htargetRepair, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    presented := presented
    sourcePresentation := hsource
    pointedProgress := D
    globalProgress := hglobal
  }

/-- The final recursive target is still the actual pointed-family target, not
a repair-only relabel of the original source. -/
@[simp]
theorem target_family
    {RR : RepairRanking}
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
      RR s complexity) :
    D.pointedProgress.target.family =
      D.pointedProgress.presentation.geometry.pointedReflectionState.family := by
  exact D.pointedProgress.target_family

end AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress

end

end HC4.Valuation
