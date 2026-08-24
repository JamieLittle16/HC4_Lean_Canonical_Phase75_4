import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockRankTwoGeometry
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurPreassemblyClosure
import Mathlib.Tactic

/-!
# A18.4.22: retain the geometry of the B38 early-Schur rank-two exits

A18.4.21 removes every repair-only rank-two exit that occurs before the
stationary closing carriers are formed.  One historical source of the same
problem remains later in the early-Schur preassembly theorem B38.

B38 itself already proves much more than `RepairProgress`:

* if the raw binary Schur line moves, it constructs a nonzero projective
  wedge, the exact negative-square derivative determinant identity, an actual
  source point where that determinant is nonzero, and a field-valued binary
  block with trivial kernel;
* if the raw line is constant but the first spatial key has transverse Hessian
  rank at least two, it constructs an actual nonzero `2 x 2` Hessian minor of
  the retained first-key source profile.

The old assembly wrapper discarded both packets before calling
`exists_outerRankTwoRepairMacro`.  This file keeps them.

As in A18.4.21, the finite rank promotion is then attached to the honest
20-fold aligned outer family only after one of these geometric witnesses has
been retained.  No new algebra is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The two actual geometric reasons B38 may promote rank one to rank two.

The constant-line constructor retains the literal line and the equality tying
its first-key assembly back to that exact Stage-3 Schur kernel. -/
inductive EarlySchurRankTwoGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
    (complexity : ℕ) : Type (u + 1)

  | rawDerivative
      (repair : C.RawSpecialSchurDerivativeRankTwoRepairData complexity)

  | firstKeyTransverse
      (line : C.ConstantSpecialSchurKernelLineData)
      (assembly : C.FirstKeyCanonicalRS2ProvenanceAssemblyData)
      (assembly_schurKernel :
        assembly.schurKernel = line.toDenominatorClearedSpecialSchurKernelData)
      (repair : C.FirstKeyTransverseRankTwoRepairData assembly.canonical complexity)

/-- Geometry-preserving B38 split.

Compared with `earlySchur_rankTwoMacro_or_constantLineRS2Preassembly`, the left
branch stops *before* the historical macro wrapper and returns the complete
rank-two packet that justified the promotion. -/
theorem earlySchur_rankTwoGeometry_or_constantLineRS2Preassembly
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (complexity : ℕ)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect) :
    Nonempty (C.EarlySchurRankTwoGeometry hlt complexity) ∨
      Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData := by
  let X : AdaptiveAlignedSmithEarlySchurFirstKeyContext P C hlt :=
    P.earlySchurFirstKeyContext C hlt
  rcases C.rawSpecialSchurProjectiveWedge_or_constantLine with hmoving | hconstant
  · rcases hmoving with ⟨k, hk⟩
    rcases C.rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
        complexity k hk with ⟨R⟩
    exact Or.inl ⟨.rawDerivative R⟩
  · rcases hconstant with ⟨L⟩
    rcases X.firstSpatialKey.exists_constantLineCanonicalProvenance L with
      ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      exact Or.inl ⟨.firstKeyTransverse L A hAE R⟩
    · rcases hrs2 with ⟨N⟩
      exact Or.inr ⟨{
        line := L
        provenance := A
        provenance_schurKernel := hAE
        rs2Ready := N
      }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Attach the B38 witness to the actual aligned outer family -/

/-- Geometry-carrying global rank-two progress for one early-Schur B38 exit. -/
structure AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  problem : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s
  carrier : AdaptiveAlignedSmithRankOneClosingSourceCarrier problem.stationary.blocker
  preterminal :
    carrier.firstActualLayerOrder <
      problem.stationary.blocker.aligned.endpoint.defect
  geometry :
    carrier.EarlySchurRankTwoGeometry preterminal complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target =
      (problem.stationary.blocker.aligned.toOuterScaleAwareState s).withRepairOnly
        (rankTwoRepairState complexity)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove
      (problem.stationary.blocker.aligned.toOuterScaleAwareState s) s
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target
      (problem.stationary.blocker.aligned.toOuterScaleAwareState s)
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- A B38 geometric packet justifies the canonical finite rank promotion on
that same honest aligned outer family. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
    (G : C.EarlySchurRankTwoGeometry hlt complexity) :
    AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
      RR s complexity := by
  let outer := P.stationary.blocker.aligned.toOuterScaleAwareState s
  let target := outer.withRepairOnly (rankTwoRepairState complexity)
  have houterRepair : outer.repair = rankOneRepairState complexity := by
    change s.repair = rankOneRepairState complexity
    exact hsrepair
  have hrepair : RepairProgress outer.repair (rankTwoRepairState complexity) := by
    simpa [houterRepair] using rankOne_to_rankTwo_repairProgress complexity
  have hpresented : CertifiedSameScaleEpisodeProgress RR target outer := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    simpa [target, outer,
      ScaleAwareAdaptiveGeometricRestartState.withRepairOnly, hsrepair] using
      repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    problem := P
    carrier := C
    preterminal := hlt
    geometry := G
    target := target
    target_eq := rfl
    sourcePresentation :=
      ⟨P.stationary.blocker.aligned.certifiedOuterInternal_of_defect_eq
        s P.clock_eq⟩
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-- The final local early-Schur branch with B38 rank-two geometry preserved.
The right constructor is exactly the old RS2-ready constant-line residue. -/
inductive AdaptiveAlignedSmithCanonicalEarlySchurGeometricPreassemblyOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | rankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
          RR s complexity))

  | constantLineRS2
      (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
      (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
      (R : Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

/-- Assembly-facing wrapper of the geometry-preserving B38 split. -/
theorem AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem.earlySchur_geometricPreassembly
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect) :
    AdaptiveAlignedSmithCanonicalEarlySchurGeometricPreassemblyOutcome
      RR s complexity := by
  rcases C.earlySchur_rankTwoGeometry_or_constantLineRS2Preassembly
      P complexity hlt with hG | hR
  · rcases hG with ⟨G⟩
    exact .rankTwoProgress
      ⟨AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress.ofGeometry
        RR P complexity hsrepair C hlt G⟩
  · exact .constantLineRS2 P C hlt hR

end

end HC4.Valuation
