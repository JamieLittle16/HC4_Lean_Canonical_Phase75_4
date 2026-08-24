import HC4.Valuation.AdaptiveAlignedSmithCanonicalNoWallUnramifiedSmith
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentationFreeExactClock
import Mathlib.Tactic

/-!
# A18.4.43: intercept positive no-wall loss before exact-clock ramification

A18.4.42 proves that a no-wall primitive Smith branch with positive minimal
zero-grade parameter order already has an honest same-scale successor on the
incoming family.  This file splices that theorem in *before* the historical
20-fold one-shot aligned endpoint is constructed.

If the canonical first Smith search has a genuine wall, we run the existing
presentation-free exact-clock frontier unchanged.  If there is no genuine
wall, let `m` be the minimal parameter order on the zero Smith grade:

* `m > 0` exits immediately by the A18.4.42 same-scale defect drop;
* `m = 0` is a zero-cost presentation case, so the existing finite exact-clock
  classifier may be used unchanged.

Thus the only no-wall branch which actually spends Hessian clock is consumed
at the original absolute scale.  No quotient-valued or cross-scale induction
coordinate is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Exact-clock frontier after removing the only strictly lossy no-wall
presentation.  The second constructor retains the complete A18.4.38 payload;
this patch deliberately changes no downstream geometry. -/
inductive AdaptiveAlignedSmithCanonicalNoWallReducedExactClockOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | sameScale
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (progress : CertifiedSameScaleEpisodeProgress RR target s)
  | exactClock
      (outcome : AdaptiveAlignedSmithCanonicalPresentationFreeExactClockOutcome
        RR s complexity)

/-- **A18.4.43 no-wall intercept.**

A positive no-wall primitive loss is never represented by the historical
factor-20 endpoint.  It is consumed immediately as same-scale progress.
Only a genuine wall or the zero-order no-wall presentation reaches the
already-green presentation-free exact-clock stack. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalNoWallReducedExactClockFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalNoWallReducedExactClockOutcome
      RR s complexity := by
  let P := zeroJetNormalizedFamily s.family
  let a := zeroPolynomialSection (K := K)
  by_cases hwall : HasAlignedSmithGenuineWall P a s.movingSection
  · exact .exactClock
      (s.alignedSmithCanonicalPresentationFreeExactClockFrontier
        RR complexity hsrepair)
  · let hne :=
      zeroSmithSourceSupport_nonempty_of_noGenuineWall
        P a s.movingSection s.rawDefect
        (by simpa [P] using s.normalized_hessianDefect) hwall
    let m := minimalZeroSmithParameterOrder P hne
    by_cases hm : m = 0
    · exact .exactClock
        (s.alignedSmithCanonicalPresentationFreeExactClockFrontier
          RR complexity hsrepair)
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hwall' :
          ¬ HasAlignedSmithGenuineWall
            (zeroJetNormalizedFamily s.family)
            (zeroPolynomialSection (K := K)) s.movingSection := by
        simpa [P, a] using hwall
      have hmpos' :
          0 < minimalZeroSmithParameterOrder
            (zeroJetNormalizedFamily s.family)
            (zeroSmithSourceSupport_nonempty_of_noGenuineWall
              (zeroJetNormalizedFamily s.family)
              (zeroPolynomialSection (K := K)) s.movingSection
              s.rawDefect s.normalized_hessianDefect hwall') := by
        simpa [P, a, hne, m] using hmpos
      rcases s.exists_sameScaleNoWallSmithSuccessor
          RR hwall' hmpos' with ⟨target, hprogress⟩
      exact .sameScale target hprogress

end

end HC4.Valuation
