import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseRees
import HC4.Valuation.FourOrdinaryReverseReesCollision
import HC4.Valuation.SeparatedRightWallScaleDescent
import Mathlib.Tactic

/-!
# Exact moving collision on the honest top-kernel reverse-Rees family

The top-kernel branch already uses the bounded reverse-weight construction with
the ordinary weight `(1,1,1,1)`.  This file identifies that family with the
standard four-variable ordinary reverse-Rees family and therefore imports its
exact moving collision from the represented determinant-one source.

The moving sections are the literal scaled marked points

    tau * 0,   tau * e₀.

This retains collision provenance through the auxiliary reverse-Rees family
without asserting that the parameter clock is a blocker clock and without
manufacturing a terminal fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The bounded ordinary-weight reverse-Rees family used by the top-kernel seam
is literally the standard four-variable ordinary reverse-Rees family. -/
theorem topKernelReverseReesFamily_eq_fourOrdinary
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.topKernelReverseReesFamily =
      fourOrdinaryReverseReesFamily
        T.topKernelReesSource T.topFace.degree := by
  apply MvPolynomial.ext
  intro d
  rw [topKernelReverseReesFamily]
  rw [reverseWeightedReesFamily_coeff]
  rw [coeff_fourOrdinaryReverseReesFamily]
  by_cases hd : d ∈ T.topKernelReesSource.support
  · simp [hd, weight_ordinaryTopNatWeight]
  · have hc : MvPolynomial.coeff d T.topKernelReesSource = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hd, hc, weight_ordinaryTopNatWeight]

/-- The represented marked collision survives as an exact polynomial-family
collision on the honest ordinary reverse-Rees interpolation. -/
theorem topKernelReverseRees_exactGradientCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasPolynomialFamilyExactGradientCollision
      T.topKernelReverseReesFamily
      (fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K)))
      (fourReverseReesScaledSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
  rw [T.topKernelReverseReesFamily_eq_fourOrdinary]
  apply fourOrdinaryReverseReesFamily_exactGradientCollision
  · intro d hd
    have h := T.topKernelReesSource_hasReverseWeightBound d hd
    simpa only [weight_ordinaryTopNatWeight] using h
  · exact T.topKernelReesSource_exactCollision

/-- The scaled zero marked point is literally the zero polynomial section. -/
theorem fourReverseReesScaledSection_zero_eq_zeroPolynomialSection :
    fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K)) =
      zeroPolynomialSection (K := K) := by
  funext i
  simp [fourReverseReesScaledSection, zeroPolynomialSection]

/-- The marked-axis scaled section is divisible by one parameter factor in
the marked coordinate, so the inverse unit source inflation is integral. -/
theorem fourReverseReesScaledSection_axisZero_unitDivisible :
    HasUnitKernelSectionDivisibility (K := K) (0 : Fin 4)
      (fourReverseReesScaledSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
  unfold HasUnitKernelSectionDivisibility
  simp [fourReverseReesScaledSection, coordinateAxisPoint]

/-- The zero scaled section is also integrally divisible in the marked
coordinate. -/
theorem fourReverseReesScaledSection_zero_unitDivisible :
    HasUnitKernelSectionDivisibility (K := K) (0 : Fin 4)
      (fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K))) := by
  rw [fourReverseReesScaledSection_zero_eq_zeroPolynomialSection]
  unfold HasUnitKernelSectionDivisibility zeroPolynomialSection
  simp

/-- Dividing the marked coordinate of `tau * e₀` by one parameter factor
recovers the literal constant section `e₀`. -/
theorem unitKernelDeflateSection_scaledAxisZero_eq_constantAxis :
    unitKernelDeflateSection (K := K) (0 : Fin 4)
        (fourReverseReesScaledSection
          (coordinateAxisPoint (K := K) (0 : Fin 4)))
        fourReverseReesScaledSection_axisZero_unitDivisible =
      polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  funext i
  by_cases hi : i = (0 : Fin 4)
  · subst i
    unfold unitKernelDeflateSection
    simp only [dif_pos rfl]
    have hspec :=
      Classical.choose_spec
        (fourReverseReesScaledSection_axisZero_unitDivisible (K := K))
    simp only [fourReverseReesScaledSection] at hspec
    change
      Polynomial.X *
          Polynomial.C
            (coordinateAxisPoint (K := K) (0 : Fin 4) 0) =
        Polynomial.X *
          Classical.choose
            (fourReverseReesScaledSection_axisZero_unitDivisible (K := K))
      at hspec
    have haxis :
        coordinateAxisPoint (K := K) (0 : Fin 4) 0 = 1 := by
      simp [coordinateAxisPoint]
    rw [haxis] at hspec
    have heq :
        Polynomial.X ^ 1 *
            Classical.choose
              (fourReverseReesScaledSection_axisZero_unitDivisible (K := K)) =
          Polynomial.X ^ 1 * Polynomial.C (1 : K) := by
      simpa [pow_one] using hspec.symm
    have hcancel :=
      polynomial_X_pow_mul_cancel (K := K) 1 heq
    simpa [polynomialConstantSection, coordinateAxisPoint] using hcancel
  · simp [unitKernelDeflateSection, fourReverseReesScaledSection,
      polynomialConstantSection, coordinateAxisPoint, hi]

/-- The inverse marked-axis source inflation also sends the scaled zero
section back to the literal zero section. -/
theorem unitKernelDeflateSection_scaledZero_eq_zero :
    unitKernelDeflateSection (K := K) (0 : Fin 4)
        (fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K)))
        fourReverseReesScaledSection_zero_unitDivisible =
      zeroPolynomialSection (K := K) := by
  exact
    unitKernelDeflateSection_eq_zero_of_eq_zero
      (K := K) (0 : Fin 4)
      (fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K)))
      fourReverseReesScaledSection_zero_unitDivisible
      fourReverseReesScaledSection_zero_eq_zeroPolynomialSection

/-- One inverse marked-axis source inflation separates the coalescing
reverse-Rees collision into constant marked sections `0 ~ e₀`. -/
noncomputable def topKernelMarkedAxisFirstContactFamily
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  kernelInflateHom (K := K) (0 : Fin 4) 1 T.topKernelReverseReesFamily

/-- The first-contact family carries the literal constant-section exact
collision `0 ~ e₀`. -/
theorem topKernelMarkedAxisFirstContact_exactGradientCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasPolynomialFamilyExactGradientCollision
      T.topKernelMarkedAxisFirstContactFamily
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
  have hcoll :=
    polynomialFamilyExactGradientCollision_kernelInflate_unit
      (K := K) (0 : Fin 4)
      T.topKernelReverseReesFamily
      (fourReverseReesScaledSection (fun _ : Fin 4 => (0 : K)))
      (fourReverseReesScaledSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)))
      fourReverseReesScaledSection_zero_unitDivisible
      fourReverseReesScaledSection_axisZero_unitDivisible
      T.topKernelReverseRees_exactGradientCollision
  rw [unitKernelDeflateSection_scaledZero_eq_zero,
    unitKernelDeflateSection_scaledAxisZero_eq_constantAxis] at hcoll
  simpa [topKernelMarkedAxisFirstContactFamily] using hcoll

/-- The associated graded fibre of the marked-axis first contact therefore
has the original two distinct marked points as an exact gradient collision. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_exactCollision
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber T.topKernelMarkedAxisFirstContactFamily)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  have hcoll :=
    polynomialFamilyExactGradientCollision_specialFiber
      T.topKernelMarkedAxisFirstContactFamily
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)))
      T.topKernelMarkedAxisFirstContact_exactGradientCollision
  simpa [polynomialSectionSpecialPoint, zeroPolynomialSection] using hcoll

/-- The first-contact associated graded collision is genuinely nontrivial. -/
theorem topKernelMarkedAxisFirstContact_specialFiber_collisionPoints_ne
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (fun _ : Fin 4 => (0 : K)) ≠
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  exact topKernelReesSource_collisionPoints_ne (K := K)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
