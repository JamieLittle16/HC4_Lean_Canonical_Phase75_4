import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3TransverseAxisInvisibility
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# The first six off-axis determinant layers of nonlinear E3 vanish exactly

At the first actual marked-axis transverse face the represented determinant-one
source admits a *new*, honestly bounded reverse-Rees family at transverse
weight cap r = D - q, rather than the old top-degree cap D.

The exact determinant-one inflation identity gives its Hessian clock

                       det Hess(Q) = tau^(4r - 6).

Since the surviving nonlinear E3 face has r >= 3, the closing clock is at
least six.  Thus every actual determinant coefficient layer at parameter
orders 0,1,2,3,4,5 vanishes *as an entire four-variable polynomial*.

This is more information than singularity of the top transverse face, but it
is not yet the needed Jacobi/cofactor identification of the first surviving
nonlinear term.  In particular, this theorem does not pretend the source
Hessian minor has an axis-detectable constant term.
-/

namespace HC4.Valuation
noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Relevel the actual determinant-one represented source at its true
highest transverse degree r.  The resulting *explicit* bounded reverse-Rees
family has the original first actual face as parameter-zero fibre and
exact Hessian determinant tau^(4r-6), with no further assumptions. -/
theorem PureLongitudinalMarkedE3Data.firstActualRelevelledDeterminantClock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let hbound :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq
    let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
      r T.topKernelReesSource hbound
    polynomialFamilySpecialFiber Q =
        familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder ∧
      HasPolynomialFamilyHessianDefect (K := K) Q (4 * r - 6) := by
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight r
      T.topKernelReesSource :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      D.coefficient_ne_zero D.topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    r T.topKernelReesSource hbound
  change
    polynomialFamilySpecialFiber Q =
        familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder ∧
      HasPolynomialFamilyHessianDefect (K := K) Q (4 * r - 6)
  constructor
  · rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
    exact (P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      D.coefficient_ne_zero D.topFace_eq).symm
  · have hr : 3 ≤ r := D.firstActualTransverseDegree_ge_three P
    have hsum :
        (∑ a : Fin 4, topKernelMarkedAxisNatWeight a) = 3 := by
      rw [Fin.sum_univ_four]
      simp [topKernelMarkedAxisNatWeight]
    have hnonneg :
        2 * (∑ a : Fin 4, topKernelMarkedAxisNatWeight a) ≤
          4 * r := by
      rw [hsum]
      omega
    have hdef := reverseWeightedReesFamily_hasHessianDefect
      topKernelMarkedAxisNatWeight r T.topKernelReesSource
      hbound T.topKernelReesSource_hessianDeterminant_eq_one hnonneg
    simpa [Q, hsum] using hdef

/-- The exact first *six* actual parameter layers of the relevelled
determinant vanish, as polynomials in all four source variables.  A
determinant-coefficient compatibility identity, not merely an
evaluation on the marked longitudinal axis. -/
theorem PureLongitudinalMarkedE3Data.firstActualRelevelledDeterminantFirstSix_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (j : ℕ) (hj : j < 6) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let hbound :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq
    let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
      r T.topKernelReesSource hbound
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant Q) j = 0 := by
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight r
      T.topKernelReesSource :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      D.coefficient_ne_zero D.topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    r T.topKernelReesSource hbound
  have hclock :=
    D.firstActualRelevelledDeterminantClock P
  change
    polynomialFamilySpecialFiber Q =
        familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder ∧
      HasPolynomialFamilyHessianDefect (K := K) Q (4 * r - 6)
      at hclock
  have hr : 3 ≤ r := D.firstActualTransverseDegree_ge_three P
  have hjs : j < 4 * r - 6 := by omega
  change familyParameterLayer
    (HC4.Polynomial.hessianDeterminant Q) j = 0
  exact hessianDefect_parameterLayer_eq_zero_of_lt Q hclock.2 hjs

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
end
end HC4.Valuation
