import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesZeroStrictLowTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSingularCarrier
import Mathlib.Tactic

/-!
# A19.54: zero-clock strict-low terminal with retained singular top face

A19.53 removed the old first-contact producer and retained the actual
zero-clock presented blocker together with an actually represented strict-low
Smith exponent.  The newer unconditional A18.5 terminal route does not use the
older terminal-cocharacter interface: at raw defect zero it replaces the
nonsingular determinant-one special fibre by its genuine nonzero maximal
ordinary top face, whose Hessian determinant is zero.

This file puts those two already-certified pieces of geometry in one carrier.
Nothing is inferred from the repair tag.  The complete rank-three geometry is
reconstructed from the actual presented blocker and its certified rank-one
repair equality, and the singular top face is selected from the actual
presented family using its literal zero raw defect.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The producer-free A19.53 terminal, now paired with the complete retained
rank-three geometry and the genuine singular maximal ordinary face of the
same presented zero-clock family. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  terminal :
    AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData (K := K) state
  geometry :
    AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
      canonicalAdaptiveAlignedSmithRepairRanking terminal.blocker 0
  presented_zero : terminal.blocker.presented.rawDefect = 0
  topFace :
    AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData
      terminal.blocker.presented

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

/-- A19.53 loses no rank-three provenance: the canonical blocker geometry can
be regenerated directly on the same actual state from its certified repair
equality. -/
noncomputable def rankThreeGeometry
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
      canonicalAdaptiveAlignedSmithRepairRanking T.blocker 0 :=
  T.blocker.allRankThreeGeometry
    canonicalAdaptiveAlignedSmithRepairRanking 0 T.repair_eq

/-- The represented blocker presentation itself is also at literal raw defect
zero.  This is the first component of the already-green A19.52 packet. -/
theorem presented_rawDefect_eq_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    T.blocker.presented.rawDefect = 0 := by
  exact T.zeroClockFirstContactPacket.1

/-- Attach the genuine A18.5.12 singular maximal ordinary face to the actual
strict-low terminal.  This is the bridge from the A19 mixed-degree packet to
the newer unconditional terminal RationalRigidity route. -/
noncomputable def toSingularTerminal
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData
      (K := K) state) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state where
  terminal := T
  geometry := T.rankThreeGeometry
  presented_zero := T.presented_rawDefect_eq_zero
  topFace :=
    T.blocker.presented.zeroDefect_singularTopFace
      T.presented_rawDefect_eq_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalData

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The retained top face is genuinely nonzero. -/
theorem topFace_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.topFace.face ≠ 0 :=
  T.topFace.face_ne_zero

/-- The retained top face is genuinely nonlinear, of ordinary degree at least
three. -/
theorem topFace_degree_ge_three
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    3 ≤ T.topFace.degree :=
  T.topFace.degree_ge_three

/-- The exact singularity needed by the A18.5 RationalRigidity terminal
machinery is now present on the same carrier as the strict-low packet. -/
theorem topFace_hessianDeterminant_eq_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Polynomial.hessianDeterminant T.topFace.face = 0 :=
  T.topFace.hessian_zero

/-- The full A19.52 strict-low packet remains available without unpacking the
new singular-face carrier. -/
theorem zeroClockFirstContactPacket
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.terminal.blocker.presented.rawDefect = 0 ∧
      T.terminal.blocker.blocker.aligned.endpoint.defect = 0 ∧
      AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        T.terminal.exponent ∧
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K)
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
        T.terminal.exponent ∧
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K)
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
        T.terminal.exponent ∧
      AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
        (longitudinalRightRecenterHom
          (K := K)
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
        (0 : Fin 4) := by
  exact T.terminal.zeroClockFirstContactPacket

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Producer-free reached outcome upgraded to the singular carrier used by the
unconditional A18.5 terminal machinery. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_zeroStrictLowSingularTerminal
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
          (K := K) T.trace.reachedRankThree.state) := by
  rcases T.globalProgress_or_zeroStrictLowTerminal hsrepair with
    hprogress | hterminal
  · exact Or.inl hprogress
  · rcases hterminal with ⟨Z⟩
    exact Or.inr ⟨Z.toSingularTerminal⟩

end

end HC4.Valuation
