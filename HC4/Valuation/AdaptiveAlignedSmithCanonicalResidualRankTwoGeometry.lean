import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockGeometryAssembly
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyLosslessAxis
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyClosingCarrierExit
import Mathlib.Tactic

/-!
# A18.4.24: retain the remaining residual rank-two geometry

A18.4.21--23 remove the repair-only rank-two interface from the initial
exact-clock assembly.  The later A17 residual reductions contain a few more
calls to the same historical wrapper.  Those calls do not hide new
mathematics: immediately before each call the repository already carries one
of five concrete source-side witnesses:

* a nonzero mixed wall-face Hessian determinant `-(P_UV)^2`;
* a nonzero intrinsic base-plane Hessian determinant;
* a moving raw Schur derivative packet with an evaluated nondegenerate block;
* a nonzero first-key transverse Hessian minor; or
* a moving cleared-lift derivative packet with an evaluated nondegenerate
  binary block.

This file gives those already-proved witnesses one common, restricted type.
Unlike a generic `RepairProgress` wrapper, the type cannot be inhabited by a
bare finite repair step: every constructor contains actual polynomial/Hessian
geometry tied to the stationary blocker.

A single global progress object then attaches the canonical rank-one ->
rank-two repair change to the honest aligned outer family *after* one of these
witnesses is present.  The two useful residual reductions are also rerun here
losslessly:

* a zero-order equality wall is either mixed/base-plane rank-two geometry or
  a genuine lossless low-dimensional axis face;
* an arbitrary retained closing carrier is either an honest ramified defect
  spend or one of the three Schur/first-key/lift rank-two geometries.

No new geometric lemma, homogeneity hypothesis, or numerical-only successor
is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Restricted geometry type for residual rank-two events -/

/-- Every remaining rank-two event on the A17 residual side, before geometry
was erased by the historical outer macro. -/
inductive AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ) : Type (u + 1)

  | wallMixed
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (wall : C.DirectClosingCanonicalSquareZeroOrderFamilyWallShape heq)
      (face : MvPolynomial (Fin 4) K)
      (U V : Fin 4)
      (repair :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingWallFaceMixedRepairData
          complexity face U V)

  | wallBasePlane
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (wall : C.DirectClosingCanonicalSquareZeroOrderFamilyWallShape heq)
      (face : MvPolynomial (Fin 4) K)
      (i j : Fin 4)
      (repair :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingWallFaceBasePlaneRankTwoRepairData
          complexity face i j)

  | rawSchurDerivative
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (repair : C.RawSpecialSchurDerivativeRankTwoRepairData complexity)

  | firstKeyTransverse
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (line : C.ConstantSpecialSchurKernelLineData)
      (assembly : C.FirstKeyCanonicalRS2ProvenanceAssemblyData)
      (assembly_schurKernel :
        assembly.schurKernel = line.toDenominatorClearedSpecialSchurKernelData)
      (repair : C.FirstKeyTransverseRankTwoRepairData
        assembly.canonical complexity)

  | clearedLiftDerivative
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (preassembly : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
      (repair : C.ConstantLineLiftDerivativeRankTwoRepairData
        preassembly complexity)

namespace AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry

/-- The finite repair transition is recovered *from* the retained geometry,
never supplied independently. -/
theorem repairProgress
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity) := by
  cases G with
  | wallMixed C heq wall face U V repair => exact repair.progress
  | wallBasePlane C heq wall face i j repair => exact repair.progress
  | rawSchurDerivative C repair => exact repair.progress
  | firstKeyTransverse C line assembly hEq repair => exact repair.repairProgress
  | clearedLiftDerivative C preassembly repair => exact repair.progress

/-- Every constructor also carries the expected strict finite repair measure. -/
theorem measure_lt
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure := by
  cases G with
  | wallMixed C heq wall face U V repair => exact repair.measure_lt
  | wallBasePlane C heq wall face i j repair => exact repair.measure_lt
  | rawSchurDerivative C repair => exact repair.measure_lt
  | firstKeyTransverse C line assembly hEq repair => exact repair.measure_lt
  | clearedLiftDerivative C preassembly repair => exact repair.measure_lt

end AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry

/-! ## Geometry-carrying global rank promotion -/

/-- Global progress for a later residual rank-two event.  The recursive target
uses the actual aligned outer family; the source presentation and the
source-side geometric witness are both retained. -/
structure AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  geometry : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
    (K := K) stationary complexity
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target =
      (stationary.blocker.aligned.toOuterScaleAwareState s).withRepairOnly
        (rankTwoRepairState complexity)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove
      (stationary.blocker.aligned.toOuterScaleAwareState s) s
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target
      (stationary.blocker.aligned.toOuterScaleAwareState s)
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- Attach the rank change only after the restricted residual geometry has
supplied its own repair certificate. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) :
    AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress
      RR s complexity := by
  let outer := S.blocker.aligned.toOuterScaleAwareState s
  let target := outer.withRepairOnly (rankTwoRepairState complexity)
  have houterRepair : outer.repair = rankOneRepairState complexity := by
    change s.repair = rankOneRepairState complexity
    exact hsrepair
  have hrepair :
      RepairProgress outer.repair (rankTwoRepairState complexity) := by
    simpa [houterRepair] using G.repairProgress
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
      G.measure_lt
  exact {
    stationary := S
    clock_eq := hclock
    geometry := G
    target := target
    target_eq := rfl
    sourcePresentation :=
      ⟨S.blocker.aligned.certifiedOuterInternal_of_defect_eq s hclock⟩
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-! ## Lossless zero-order wall reduction -/

/-- A canonical zero-order equality wall either exposes genuine rank-two
curvature or reaches the already-green lossless low-dimensional axis packet. -/
theorem AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareZeroOrderFamilyWallShape.residualRankTwoGeometry_or_losslessAxis
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
    (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
    (wall : C.DirectClosingCanonicalSquareZeroOrderFamilyWallShape heq)
    (complexity : ℕ) :
    Nonempty (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
      (K := K) S complexity) ∨
      Nonempty (C.DirectClosingCanonicalSquareLosslessAxisTerminalCoreData heq) := by
  cases wall.toLosslessOutcome complexity with
  | mixedRepair face U V repair =>
      exact Or.inl ⟨.wallMixed C heq wall face U V repair⟩
  | basePlaneRepair face i j repair =>
      exact Or.inl ⟨.wallBasePlane C heq wall face i j repair⟩
  | losslessAxis data =>
      exact Or.inr ⟨data⟩

/-! ## Universal closing-carrier exit without geometry erasure -/

/-- Geometry-preserving replacement for
`closingCarrier_ramifiedSpend_or_rankTwoMacro`.

The proof is the same source-honest case split, but the right side returns the
actual packet which justifies rank two instead of immediately discarding it. -/
theorem AdaptiveAlignedSmithCanonicalTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (P : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (complexity : ℕ)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s) ∨
      Nonempty (AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
        (K := K) S complexity) := by
  have hpos :
      (positiveTransverseSourceSupport
        (polynomialFamilySpecialFiber C.family)).Nonempty := by
    rcases S.specialFiber_witnesses.1 with ⟨d, hd, hd1⟩
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.family] using hd
    · unfold pureLongitudinalTransverseDegree
      omega
  have hkey : C.HasFirstTransverseSourceKey :=
    C.hasFirstTransverseSourceKey_of_positiveSupport hpos

  rcases C.rawSpecialSchurProjectiveWedge_or_constantLine with hmoving | hconstant
  · rcases hmoving with ⟨k, hk⟩
    rcases C.rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
        complexity k hk with ⟨R⟩
    exact Or.inr ⟨.rawSchurDerivative C R⟩

  · rcases hconstant with ⟨L⟩
    rcases hkey.exists_constantLineCanonicalProvenance L with ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      exact Or.inr ⟨.firstKeyTransverse C L A hAE R⟩
    · rcases hrs2 with ⟨N⟩
      let R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData := {
        line := L
        provenance := A
        provenance_schurKernel := hAE
        rs2Ready := N
      }
      rcases R.constantSourceKernel_or_activeProjective with hkernel | hactive
      · rcases hkernel with ⟨K0⟩
        let literal := K0.toLiteralConstantSpecialSourceKernelData
        have htrans := P.exists_transverse_of_literalConstantKernel literal
        exact Or.inl
          (literal.exists_ramifiedSpend_of_transverse S clock_eq htrans)
      · rcases hactive with ⟨M⟩
        let E := M.toEulerMotionData
        rcases E.exists_liftDerivativeRankTwoRepairData complexity with ⟨R2⟩
        exact Or.inr ⟨.clearedLiftDerivative C R R2⟩

end

end HC4.Valuation