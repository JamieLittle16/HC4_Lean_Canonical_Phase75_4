import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidSourceCompression

/-!
# Final assembly A17.3A: post-rigid-source-compression frontier

The A17.2B frontier has three local constructors.  This adapter merges the two
rigid packet variants into the source-complete rigid obstruction introduced in
`FinalAssemblyRigidSourceCompression`.  No descent claim is made: every
strict spend and rank-two macro is transported unchanged.

After this file the local frontier has exactly two species:

* source-ready zero-Schur;
* source-complete all-minors rigid.

That is the minimal algebraic frontier for the final local eliminator.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A17.3A outcome with only two local obstruction species. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidSourceCompressionOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | local (P : AdaptiveAlignedSmithCanonicalRigidCompressedTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.3A source-complete rigid compression.**

The two rigid packet constructors differ only in their concrete persistent
packet witness.  They are merged here while retaining the exact common source
packet and full all-minors certificate. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePostRigidSourceCompressionFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidSourceCompressionOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostClosingCarrierFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      cases P.geometry with
      | zeroSchurSourceReady C source =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .zeroSchurSourceReady C source
          }
      | planarRigid hall Q hrigid =>
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction
              P.stationary := {
            source := P.source
            hall := hall
            packet := .planar Q hrigid
          }
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rigid R
          }
      | wSquareRigid hall Q hrigid =>
          let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction
              P.stationary := {
            source := P.source
            hall := hall
            packet := .wSquare Q hrigid
          }
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rigid R
          }

end

end HC4.Valuation
