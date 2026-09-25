import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisLinearPowerFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidTopKernel
import Mathlib.Tactic

/-!
# E2: cross-facet marked-axis linear powers collapse to codimension two

The E1 top-kernel frontier has a genuine cross-facet constructor on the actual
singular maximal ordinary top face.  Generic homogeneous-ray analysis of such a
crossing leaves three possibilities:

* a codimension-two near endpoint;
* a codimension-two far endpoint; or
* a nonzero principal Hessian minor on the original source face.

In the present top-kernel branch that source face is already a scalar multiple
of one linear form to a power.  Its Hessian has rank at most one, so every
`2 x 2` minor vanishes identically.  Hence the rank-two alternative is
impossible and the cross-facet branch reaches an explicit codimension-two
endpoint.

This file is a refinement only.  It does not identify either endpoint with the
canonical A19 codimension-two vertex and does not promote it to a terminal
contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Every Hessian `2 x 2` minor of the top linear power vanishes. -/
theorem topFace_allTwoByTwoMinors_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    ∀ i j k l : Fin 4,
      HC4.Polynomial.hessian T.topFace.face i j *
            HC4.Polynomial.hessian T.topFace.face k l -
          HC4.Polynomial.hessian T.topFace.face i l *
            HC4.Polynomial.hessian T.topFace.face k j = 0 := by
  intro i j k l
  have hm2 : 2 ≤ T.topFace.degree := by
    have hm3 := T.topFace.degree_ge_three
    omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, T.topFace.degree = n + 2 := by
    exact ⟨T.topFace.degree - 2,
      (Nat.sub_add_cancel hm2).symm⟩
  rw [P.eq_power, hn]
  repeat' rw [hessian_C_mul_gradientRatioLinearForm_pow_add_two_finFour]
  simp only [MvPolynomial.C_mul]
  ring

/-- In particular every principal Hessian minor of the linear-power top face
vanishes. -/
theorem topFace_hessianPrincipalMinor_eq_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor T.topFace.face i j = 0 := by
  unfold HC4.Polynomial.hessianPrincipalMinor
  exact P.topFace_allTwoByTwoMinors_zero i i j j

/-- The actual E1 top-face crossing canonically supplies a balance-free
coordinate-zero ray on the same top face. -/
noncomputable def markedAxisCrossFacetRay
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : CrossFacetInitialData T.topFace.face
      (crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) :
    CrossFacetRayData T.topFace.face (0 : Fin 4) := by
  have hzero :
      (zeroCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty :=
    ⟨D.facetExponent,
      mem_zeroCoordinateSupport.mpr
        ⟨D.facet_mem, D.facet_coordinate_zero⟩⟩
  have hpos :
      (positiveCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty :=
    ⟨D.outsideExponent,
      mem_positiveCoordinateSupport.mpr
        ⟨D.outside_mem, D.outside_coordinate_pos⟩⟩
  exact crossFacetRayData hzero hpos

/-- Explicit endpoint data left by the cross-facet marked-axis branch. -/
inductive MarkedAxisCrossFacetCodimensionTwoFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : CrossFacetInitialData T.topFace.face
      (crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) : Prop
  | near
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.markedAxisCrossFacetRay D).renameContactToZero.facetExponent)
  | far
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (((P.markedAxisCrossFacetRay D).renameContactToZero).zeroAffineLineData.exponent
            (((P.markedAxisCrossFacetRay D).renameContactToZero)
              .zeroCoefficientPolynomial.natDegree)))

/-- **E2 cross-facet refinement.**

A marked-axis cross-facet branch of a top-face linear power reaches one of the
two explicit codimension-two endpoints of its honest normalized ray. -/
theorem markedAxisCrossFacet_codimensionTwoFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : CrossFacetInitialData T.topFace.face
      (crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) :
    P.MarkedAxisCrossFacetCodimensionTwoFrontier D := by
  let R := P.markedAxisCrossFacetRay D
  have hhom :
      ∀ d ∈ T.topFace.face.support,
        HC4.Polynomial.ordinaryDegree4 d = T.topFace.degree := by
    intro d hd
    exact T.topFace.face_support_ordinaryDegree_eq hd
  rcases balanceFreeHomogeneousRay_codimensionTwo_or_sourceRankTwo
      R T.topFace.hessian_zero hhom with
    hnear | hfar | hminor
  · exact .near (by simpa [R] using hnear)
  · exact .far (by simpa [R] using hfar)
  · rcases hminor with ⟨i, j, _hij, hne⟩
    exact (hne (P.topFace_hessianPrincipalMinor_eq_zero i j)).elim

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
