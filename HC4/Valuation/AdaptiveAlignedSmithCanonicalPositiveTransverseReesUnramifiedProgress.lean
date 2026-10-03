import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesUnramifiedReentry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# A19.32: package the unramified Rees re-entry as an A18 trace edge

A19.31 constructs an honest same-scale state at every strict early positive
Rees frontier.  Its raw Hessian clock is strictly smaller and the repair tag is
unchanged.  Those are exactly the hypotheses already used by A18.4.109's
`restart` constructor.

This file adds only the existing global-macro certificate.  It introduces no
new progress relation and no new termination measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **A19.32 honest A18 restart edge.**

A strict early positive Rees frontier gives the exact triple consumed by the
existing rank-one termination trace: global macro progress, strict natural raw
clock decrease, and unchanged repair metadata. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.exists_canonicalPositiveTransverseRees_unramifiedProgress
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < source.rawDefect)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      source.rawDefect source.family)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight
      source.rawDefect source.movingSection < source.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source ∧
      target.rawDefect < source.rawDefect ∧
      target.repair = source.repair := by
  rcases source.exists_canonicalPositiveTransverseRees_unramifiedReentry
      hpositive hbound hlt with
    ⟨target, hraw, hscale, hdegree, hcomplexity, hrepair, hltRaw⟩
  have hsame : SameEpisodeScale target source := by
    exact hscale
  have hcert :=
    certifiedAdaptiveAlignedSmithCanonicalGlobalMacroProgress_of_rawDefect_lt
      (K := K) (t := target) (s := source) hsame hrepair hltRaw
  exact ⟨target, hcert.progress, hltRaw, hrepair⟩

end

end HC4.Valuation
