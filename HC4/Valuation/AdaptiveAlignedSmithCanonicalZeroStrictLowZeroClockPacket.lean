import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowMixedDegree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankThree
import Mathlib.Tactic

/-!
# A19.51: exact zero-clock packet for the final strict-low blocker

The source-to-presented move on a canonical presented blocker is a certified
pure ramified presentation.  Its raw clock is therefore multiplied by a
positive ramification factor.  In particular a zero source clock remains
literally zero on the represented state, and hence on the represented blocker
endpoint itself.

Combined with A19.50, the final strict-low residue simultaneously carries:

* literal raw defect zero on the represented state and blocker;
* an honest exact active special-fibre Hessian chart and complete rank-three
  geometry on that represented state;
* the explicit two-endpoint strict-low residual normal form;
* exact same-Smith-exponent mixed ordinary-degree support; and
* the canonical first longitudinal departure at that same exponent.

This is a lossless description of the genuine final local problem.  No
positive exact clock, terminal cocharacter, JC2 input, or progress claim is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- Zero raw defect reflects forward through the blocker's certified pure
presentation. -/
theorem presented_rawDefect_eq_zero_of_source_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hzero : source.rawDefect = 0) :
    D.presented.rawDefect = 0 := by
  rcases D.sourcePresentation with ⟨hmove⟩
  rw [hmove.raw_eq, hzero, mul_zero]

/-- Consequently the represented canonical blocker itself has zero Hessian
clock. -/
theorem blocker_defect_eq_zero_of_source_zero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hzero : source.rawDefect = 0) :
    D.blocker.aligned.endpoint.defect = 0 := by
  rw [D.defect_eq]
  exact D.presented_rawDefect_eq_zero_of_source_zero hzero

/-- The represented zero-clock state has the existing honest exact active
rank-three geometry, without changing repair state or presentation. -/
noncomputable def zeroStrictLow_completeRankThreeGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hzero : source.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
      D.presented complexity :=
  D.presented.zeroDefect_completeRankThreeGeometry complexity
    (D.presented_rawDefect_eq_zero_of_source_zero hzero)

/-- Consolidated final zero-clock packet, stated propositionally so no witness
choice is hidden. -/
theorem zeroStrictLow_zeroClockPacket
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (hzero : source.rawDefect = 0)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    D.presented.rawDefect = 0 ∧
      D.blocker.aligned.endpoint.defect = 0 ∧
      AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
        (polynomialFamilySpecialFiber D.presented.family) e ∧
      ExactSmithExponentMixedDegreeData
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e ∧
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K) (polynomialFamilySpecialFiber D.presented.family)) e := by
  have hseed := D.zeroStrictLow_stationarySeed e he hpattern
  exact ⟨
    D.presented_rawDefect_eq_zero_of_source_zero hzero,
    D.blocker_defect_eq_zero_of_source_zero hzero,
    hseed.1,
    hseed.2.1,
    hseed.2.2
  ⟩

end AdaptiveAlignedSmithCanonicalPresentedBlocker

end

end HC4.Valuation
