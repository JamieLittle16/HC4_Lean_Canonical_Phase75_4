import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureReverseReesRelevel
import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# Source-honest pure-marked auxiliary macro step

The pure-longitudinal marked-axis family is an *auxiliary* family built from a
literal zero-clock represented source.  At its first actual positive order j
the full auxiliary family is divisible by tau^j; the exact quotient is the
reverse-Rees family of that same represented determinant-one source with the
strictly smaller transverse cap r = D-j.

Both families can be made into genuine scale-aware A18 geometric states, at
the same chosen scale and repair value.  Their raw clocks are 4D-6 and 4r-6,
respectively, and the second is a certified strict global macro successor
*of the auxiliary first-contact state*.

This does NOT assert a strict successor of the original zero-clock represented
terminal.  The latter would reverse a zero raw-clock and is not a valid
application of the global termination measure.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Bounded reverse-Rees interpolation never creates a new source exponent. -/
theorem reverseWeightedReesFamily_support_subset_source
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F) :
    (reverseWeightedReesFamily w D F hbound).support ⊆ F.support := by
  intro d hd
  by_contra hnot
  have hne :
      MvPolynomial.coeff d (reverseWeightedReesFamily w D F hbound) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [reverseWeightedReesFamily_coeff, if_neg hnot] at hne
  exact hne rfl

/-- Reverse Rees preserves any nonlinear *ordinary* source-degree bound,
even when its weight function is anisotropic. -/
theorem nonlinearDegreeBound_reverseWeightedReesFamily
    (w : Fin 4 → ℕ) (D m : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (hdegree : NonlinearDegreeBound m F) :
    NonlinearDegreeBound m (reverseWeightedReesFamily w D F hbound) :=
  nonlinearDegreeBound_of_support_subset hdegree
    (reverseWeightedReesFamily_support_subset_source w D F hbound)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **Auxiliary A18 macro restart from the reached pure-longitudinal E3
geometry.**

The source underlying both new states is the original represented determinant-
one polynomial, and the two points remain the original distinct marked
points.  The strict raw-clock drop is an honest macro edge between the two
*auxiliary* states.  No strict progress from the original zero-clock state is
claimed or needed to construct this pair. -/
theorem pureLongitudinal_exists_auxiliaryMacroStep
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    ∃ s t : ScaleAwareAdaptiveGeometricRestartState (K := K),
      s.family = T.topKernelMarkedAxisFirstContactFamily ∧
      t.family =
        firstActualDeformationFamily T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer ∧
      s.degreeCap = T.topFace.degree ∧
      t.degreeCap = T.topFace.degree ∧
      s.scale = T.terminal.blocker.presented.scale ∧
      t.scale = s.scale ∧
      t.repair = s.repair ∧
      t.rawDefect < s.rawDefect ∧
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress t s := by
  let D := T.topFace.degree
  let j := T.topKernelMarkedAxisFirstActualLayerOrder
  let r := D - j
  let base := T.terminal.blocker.presented
  let F := T.topKernelReesSource
  let hnew : HasReverseWeightBound topKernelMarkedAxisNatWeight r F :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      coefficient_ne_zero topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight r F hnew
  have hdegF : NonlinearDegreeBound D F := by
    simpa [D, F, topKernelReesSource] using
      T.representedSpecialFiber_nonlinearDegreeBound_topFace
  have hdegS : NonlinearDegreeBound D
      T.topKernelMarkedAxisFirstContactFamily := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees]
    exact nonlinearDegreeBound_reverseWeightedReesFamily
      topKernelMarkedAxisNatWeight D D F
      T.topKernelReesSource_hasMarkedAxisReverseWeightBound hdegF
  have hdegQ : NonlinearDegreeBound D Q :=
    nonlinearDegreeBound_reverseWeightedReesFamily
      topKernelMarkedAxisNatWeight r D F hnew hdegF
  have hsourceClock :
      HasPolynomialFamilyHessianDefect (K := K)
        T.topKernelMarkedAxisFirstContactFamily (4 * D - 6) := by
    have hclock : T.topKernelOrdinaryReesDefect + 2 = 4 * D - 6 := by
      dsimp [D, topKernelOrdinaryReesDefect]
      omega
    rw [← hclock]
    exact T.topKernelMarkedAxisFirstContact_hasHessianDefect
  have htargetClock : HasPolynomialFamilyHessianDefect (K := K)
      Q (4 * r - 6) := by
    have h := P.pureLongitudinal_firstActualQuotient_reducedClock
      coefficient_ne_zero topFace_eq
    have hQ : HasPolynomialFamilyHessianDefect (K := K)
        (firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer)
        (4 * r - 6) := h.1
    have heq := P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
      coefficient_ne_zero topFace_eq
    change
      firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer = Q at heq
    rwa [heq] at hQ
  have htargetCollision : HasPolynomialFamilyExactGradientCollision
      Q (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
    have h := P.pureLongitudinal_firstActualQuotient_exactCollision
      coefficient_ne_zero topFace_eq
    have heq := P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
      coefficient_ne_zero topFace_eq
    change
      firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer = Q at heq
    rwa [heq] at h
  let s : ScaleAwareAdaptiveGeometricRestartState (K := K) := {
    rawDefect := 4 * D - 6
    scale := base.scale
    scale_pos := base.scale_pos
    degreeCap := D
    sourceComplexity := base.sourceComplexity
    repair := base.repair
    family := T.topKernelMarkedAxisFirstContactFamily
    movingSection := polynomialConstantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4))
    hessianDefect := hsourceClock
    nonlinearDegreeBound := hdegS
    exactCollision := by
      simpa [zeroPolynomialSection] using
        T.topKernelMarkedAxisFirstContact_exactGradientCollision
    sectionSpecial :=
      polynomialSectionSpecialPoint_constantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))
  }
  let t : ScaleAwareAdaptiveGeometricRestartState (K := K) := {
    rawDefect := 4 * r - 6
    scale := base.scale
    scale_pos := base.scale_pos
    degreeCap := D
    sourceComplexity := base.sourceComplexity
    repair := base.repair
    family := Q
    movingSection := polynomialConstantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4))
    hessianDefect := htargetClock
    nonlinearDegreeBound := hdegQ
    exactCollision := by
      simpa [zeroPolynomialSection] using htargetCollision
    sectionSpecial :=
      polynomialSectionSpecialPoint_constantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))
  }
  have hcap : 4 * r - 6 < 4 * D - 6 := by
    have hbounds :=
      P.pureLongitudinal_firstActual_transverseDegree_bounds
        coefficient_ne_zero topFace_eq
    dsimp [r, D, j]
    omega
  have hmacro : AdaptiveAlignedSmithCanonicalGlobalMacroProgress t s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
      AdaptiveAlignedSmithCanonicalGlobalMacroKey.Lt
      ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.right
    apply Prod.Lex.left
    exact hcap
  have htEq : t.family =
      firstActualDeformationFamily T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer := by
    dsimp [t]
    exact
      (P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
        coefficient_ne_zero topFace_eq).symm
  exact ⟨s, t, rfl, htEq, rfl, rfl, rfl, rfl, rfl, hcap, hmacro⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
