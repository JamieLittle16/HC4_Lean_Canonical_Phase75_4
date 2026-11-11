import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3NonlinearConcreteFrontier
import HC4.Valuation.ReverseWeightedReesHessianPrincipalMinor
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import Mathlib.Tactic

/-!
# E3 nonlinear lower-face principal-minor lift to the original source

The first actual marked-axis lower face is NOT an arbitrary later layer
of the source's original top-level reverse-Rees family.  It is exactly
the parameter-zero special fibre of a newly *relevelled* reverse-Rees
family at the maximal transverse weight r = D - j.

This observation makes principal Hessian-minor lifting sound: a nonzero
minor on the special fibre implies a nonzero whole-family minor, which
then lifts through the injective diagonal inflation to the unchanged
represented determinant-one source.

No mixed-product cancellation between different parameter layers can
invalidate this argument.  The theorem requires a nonzero principal
minor on the actual first layer; it does not assume that one has yet
been derived in every nonlinear boundary outcome.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Principal Hessian minors commute with specialization at the
zero parameter of a polynomial family. -/
theorem hessianPrincipalMinor_polynomialFamilySpecialFiber
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber Q) i j =
      MvPolynomial.map Polynomial.constantCoeff
        (HC4.Polynomial.hessianPrincipalMinor Q i j) := by
  unfold HC4.Polynomial.hessianPrincipalMinor
  simp only [hessian_polynomialFamilySpecialFiber,
    Matrix.map_apply, map_mul, map_sub]

/-- A principal minor nonzero on the special fibre is nonzero
in the entire polynomial family; this implication is valid even
when later layers have arbitrary cross terms. -/
theorem hessianPrincipalMinor_family_ne_zero_of_specialFiber
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber Q) i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor Q i j ≠ 0 := by
  intro hzero
  have hspecial := hessianPrincipalMinor_polynomialFamilySpecialFiber Q i j
  rw [hzero, map_zero] at hspecial
  exact hminor hspecial

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **Exact principal-minor source lift for the reachable first actual
marked-axis lower face.**  The face is the maximal weight component of
the *same* represented source at the reduced weight cap r, and so its
nonzero principal Hessian minor lifts to a polynomial principal minor
of the original source.  No extra collision, repair, or clock
hypothesis is introduced. -/
theorem PureLongitudinalMarkedE3Data.firstActualPrincipalMinor_sourceLift
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
      T.topKernelReesSource i j ≠ 0 := by
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let hbound :
      HasReverseWeightBound topKernelMarkedAxisNatWeight r
        T.topKernelReesSource :=
    P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
      D.coefficient_ne_zero D.topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    r T.topKernelReesSource hbound
  have hface :
      polynomialFamilySpecialFiber Q =
        familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder := by
    rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily]
    exact (P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      D.coefficient_ne_zero D.topFace_eq).symm
  have hminorFace :
      HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber Q) i j ≠ 0 := by
    rw [hface]
    exact hminor
  have hminorFamily :
      HC4.Polynomial.hessianPrincipalMinor Q i j ≠ 0 :=
    hessianPrincipalMinor_family_ne_zero_of_specialFiber Q i j hminorFace
  exact reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    topKernelMarkedAxisNatWeight r T.topKernelReesSource
    hbound i j hminorFamily

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
