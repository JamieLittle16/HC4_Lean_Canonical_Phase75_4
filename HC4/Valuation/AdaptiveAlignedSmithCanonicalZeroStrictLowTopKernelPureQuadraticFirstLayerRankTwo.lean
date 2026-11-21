import HC4.Valuation.QuadraticAxisReverseReesSpecialFiberRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureReverseReesRelevel
import Mathlib.Tactic

/-!
# Rank-two origin Hessian of the reached quadratic first-actual layer

The first-actual quotient of a reachable pure longitudinal marked-axis
branch is the reverse-Rees family of the ACTUAL represented source at
reduced level r.  If r=2, its special fibre is the original marked
first-positive coefficient layer and has a real transverse 2x2 origin
Hessian minor, despite its Hessian determinant being zero.

This transfers the source-honest quadratic-axis minor to the actual
E3 lower face.  No invented endpoint, rank promotion or assumption.
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

/-- The quadratic E3 branch has an actual rank-two transverse Hessian minor
on its FIRST NONZERO marked-axis parameter layer (not merely on the
determinant-one represented source). -/
theorem pureLongitudinal_quadraticFirstActualLayer_transverseRankTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let G := familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder
    let H := quadraticFamilyHessianMatrix G
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 := by
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
      T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    2 T.topKernelReesSource hbound
  have hQ :
      firstActualDeformationFamily
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer = Q := by
    have heq :=
      P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
        coefficient_ne_zero topFace_eq
    simpa [Q, hbound, hr] using heq
  have hface :
      familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder =
        polynomialFamilySpecialFiber Q := by
    have heq := congrArg polynomialFamilySpecialFiber hQ
    rw [firstActualDeformationFamily_specialFiber] at heq
    exact heq
  have hminor :=
    quadraticAxisReverseRees_specialFiber_transverseRankTwo
      T.topKernelReesSource hbound
      T.topKernelReesSource_hessianDeterminant_eq_one
  dsimp only at hminor ⊢
  rw [← hface] at hminor
  exact hminor

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
