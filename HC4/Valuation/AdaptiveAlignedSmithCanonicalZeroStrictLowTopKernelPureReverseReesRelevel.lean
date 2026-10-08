import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureFirstLayerCollision
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Exact strict relevel of the pure-longitudinal marked-axis reverse-Rees family

The old pure top face has no transverse monomials at the top weight `D`.
The first positive parameter order `j` gives a sharper, verified weight
bound `weight(d) ≤ D-j` on *every* represented-source monomial.

Hence the honest reverse-Rees family at level D is exactly tau^j times the
reverse-Rees family of the SAME represented source at level r=D-j.  Using
the canonical first-actual factorisation and cancellation gives

  firstActualDeformationFamily (reverseRees D) = reverseRees r.

No source terms are lost and no abstract repair or endpoint is assumed.
The smaller relevelled family carries the previously proved exact collision
and pure Hessian clock 4r-6.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Lowering the reverse-Rees level from D to D-j, under an honest
stronger source weight bound, is EXACTLY division by tau^j. -/
theorem reverseWeightedReesFamily_relevel_factor
    (w : Fin 4 → ℕ) (D j : ℕ) (F : MvPolynomial (Fin 4) K)
    (hD : HasReverseWeightBound w D F)
    (hj : j ≤ D)
    (hnew : HasReverseWeightBound w (D - j) F) :
    reverseWeightedReesFamily w D F hD =
      MvPolynomial.C (Polynomial.X ^ j) *
        reverseWeightedReesFamily w (D - j) F hnew := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [reverseWeightedReesFamily_coeff, MvPolynomial.coeff_C_mul,
    reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ F.support
  · simp only [hd, if_true]
    have hw := hnew d hd
    have hsplit :
        D - Finsupp.weight w d =
          j + (D - j - Finsupp.weight w d) := by
      omega
    rw [hsplit, pow_add]
    ring
  · simp [hd]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The canonical first-actual quotient is literally the smaller-level
reverse-Rees family of the unchanged represented determinant-one source.
The proof compares two exact whole-family factorizations and cancels the
nonzero parameter monomial. -/
theorem pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    let j := T.topKernelMarkedAxisFirstActualLayerOrder
    let r := T.topFace.degree - j
    let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight
      r T.topKernelReesSource :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
    firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer =
      reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        r T.topKernelReesSource hbound := by
  let j := T.topKernelMarkedAxisFirstActualLayerOrder
  let r := T.topFace.degree - j
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight
      r T.topKernelReesSource :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      coefficient_ne_zero topFace_eq
  let Q := firstActualDeformationFamily
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  have hzero :=
    P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq
  have hQfact :
      T.topKernelMarkedAxisFirstContactFamily =
        MvPolynomial.C (Polynomial.X ^ j) * Q := by
    have h := firstActualDeformationFamily_factorisation
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    rw [hzero] at h
    simpa [Q, j, topKernelMarkedAxisFirstActualLayerOrder,
      constantPolynomialFamily] using h
  have hjle : j ≤ T.topFace.degree := by
    exact T.topKernelMarkedAxisFirstActualLayerOrder_le_topFaceDegree
  have hRfact :
      T.topKernelMarkedAxisFirstContactFamily =
        MvPolynomial.C (Polynomial.X ^ j) *
          reverseWeightedReesFamily topKernelMarkedAxisNatWeight
            r T.topKernelReesSource hbound := by
    rw [T.topKernelMarkedAxisFirstContactFamily_eq_reverseWeightedRees]
    exact reverseWeightedReesFamily_relevel_factor
      topKernelMarkedAxisNatWeight T.topFace.degree j
      T.topKernelReesSource
      T.topKernelReesSource_hasMarkedAxisReverseWeightBound
      hjle hbound
  have hunit :
      (MvPolynomial.C (Polynomial.X ^ j) :
        MvPolynomial (Fin 4) (Polynomial K)) ≠ 0 := by
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero j Polynomial.X_ne_zero)
  have hmul :
      MvPolynomial.C (Polynomial.X ^ j) * Q =
        MvPolynomial.C (Polynomial.X ^ j) *
          reverseWeightedReesFamily topKernelMarkedAxisNatWeight
            r T.topKernelReesSource hbound :=
    hQfact.symm.trans hRfact
  have hEq : Q =
      reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        r T.topKernelReesSource hbound :=
    mul_left_cancel₀ hunit hmul
  exact hEq

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
