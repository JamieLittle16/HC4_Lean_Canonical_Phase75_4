import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureLongitudinalFirstContact
import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import Mathlib.Tactic

/-!
# First actual pure-longitudinal layer retains the marked collision

The pure-longitudinal top face has identically zero marked-axis special fibre.
The honest potential family therefore factors as

    P = X^j Q,

where j is its first positive actual parameter order and the special fibre of
Q is the genuine first actual potential layer P_j.

The whole family carries an exact gradient collision at the two constant
marked points.  Cancelling X^j in the evaluated partial derivatives shows
that Q, and hence P_j, carries the same exact collision.

This is a reachable, nonzero, lower-degree singular potential with an honest
collision, not a hypothetical exact-closing square or a new final-resolution
axiom.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A family with zero special fibre has a first-actual quotient preserving
any exact gradient collision between polynomial sections.  This is a
polynomial identity, not merely a collision at one parameter value. -/
theorem firstActualDeformationFamily_exactCollision_of_zeroSpecialFiber
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (hpositive : HasPositiveActualParameterLayer F)
    (hzero : polynomialFamilySpecialFiber F = 0)
    (a b : Fin 4 → Polynomial K)
    (hcollision : HasPolynomialFamilyExactGradientCollision F a b) :
    HasPolynomialFamilyExactGradientCollision
      (firstActualDeformationFamily F hpositive) a b := by
  let j := firstPositiveActualParameterOrder F hpositive
  let Q := firstActualDeformationFamily F hpositive
  have hfactor : F = MvPolynomial.C (Polynomial.X ^ j) * Q := by
    have h := firstActualDeformationFamily_factorisation F hpositive
    rw [hzero] at h
    simpa [j, Q] using h
  intro i
  have heval (p : Fin 4 → Polynomial K) :
      MvPolynomial.eval p (MvPolynomial.pderiv i F) =
        Polynomial.X ^ j * MvPolynomial.eval p (MvPolynomial.pderiv i Q) := by
    rw [hfactor]
    simp [MvPolynomial.pderiv_C_mul]
  have hc := hcollision i
  rw [heval a, heval b] at hc
  exact mul_left_cancel₀ (pow_ne_zero j Polynomial.X_ne_zero) hc

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **Reachable pure E3 first-layer collision.**

The true first actual marked-axis coefficient potential inherits the exact
distinct gradient collision at zero and the unit longitudinal source point.
It retains the source geometry, as opposed to the unreachable exact-closing
fresh-square assumption. -/
theorem pureLongitudinal_firstActualLayer_exactCollision
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    HasExactGradientCollision
      (familyParameterLayer
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstActualLayerOrder)
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
  let F := T.topKernelMarkedAxisFirstContactFamily
  let hp := T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  have hzero :
      polynomialFamilySpecialFiber F = 0 :=
    P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq
  have hquot :=
    firstActualDeformationFamily_exactCollision_of_zeroSpecialFiber
      F hp hzero
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)))
      T.topKernelMarkedAxisFirstContact_exactGradientCollision
  have hspecial :=
    polynomialFamilyExactGradientCollision_specialFiber
      (firstActualDeformationFamily F hp)
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4)))
      hquot
  rw [firstActualDeformationFamily_specialFiber] at hspecial
  simpa [F, hp, topKernelMarkedAxisFirstActualLayerOrder,
    polynomialSectionSpecialPoint, zeroPolynomialSection] using hspecial

/-- The pure E3 first actual layer is a nonzero lower-degree
Hessian-singular potential with an exact marked gradient collision. -/
theorem pureLongitudinal_firstActualLayer_singularCollisionPacket
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    let L := familyParameterLayer
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstActualLayerOrder
    L ≠ 0 ∧
      HC4.Polynomial.hessianDeterminant L = 0 ∧
      HasExactGradientCollision L
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) ∧
      (∀ d ∈ L.support,
        HC4.Polynomial.ordinaryDegree4 d < T.topFace.degree) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact firstPositiveActualParameterLayer_ne_zero
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  · exact P.pureLongitudinal_markedAxis_firstActualLayer_hessian_zero
      coefficient_ne_zero topFace_eq
  · exact P.pureLongitudinal_firstActualLayer_exactCollision
      coefficient_ne_zero topFace_eq
  · exact P.pureLongitudinal_markedAxis_firstActualLayer_ordinaryDegree_lt_topFace
      coefficient_ne_zero topFace_eq

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
