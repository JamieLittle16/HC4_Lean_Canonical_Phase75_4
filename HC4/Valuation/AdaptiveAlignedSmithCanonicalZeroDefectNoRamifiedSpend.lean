import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedProgressUpgrade
import Mathlib.Tactic

/-!
# No ramified defect spend can leave a zero-clock state

A certified ramified raw-defect spend strictly lowers the represented scaled
defect by cross multiplication.  If the source raw defect is literally zero,
its scaled defect is zero at every positive absolute scale, so such a strict
spend is impossible.

This is the arithmetic terminal consumer needed by the A19 codimension-two
constant-kernel route.  It does not assert well-foundedness of arbitrary
rational scales; it only observes that nothing is strictly below zero.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A raw-zero scale-aware state admits no propositionally packaged certified
ramified defect spend. -/
theorem no_certifiedRamifiedRawDefectSpend_of_rawDefect_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    ¬ ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rintro ⟨target, hspend⟩
  have hlt := hspend.scaledDefect_lt
  change target.rawDefect * s.scale < s.rawDefect * target.scale at hlt
  rw [hzero] at hlt
  simp at hlt

/-- Pointwise form convenient when a kernel consumer has already constructed
the target. -/
theorem certifiedRamifiedRawDefectSpend_impossible_of_rawDefect_zero
    {s target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hzero : s.rawDefect = 0)
    (hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s) :
    False := by
  exact no_certifiedRamifiedRawDefectSpend_of_rawDefect_zero s hzero
    ⟨target, hspend⟩

end

end HC4.Valuation
