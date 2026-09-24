import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseRees
import HC4.Valuation.FourOrdinaryReverseReesCollision
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

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
