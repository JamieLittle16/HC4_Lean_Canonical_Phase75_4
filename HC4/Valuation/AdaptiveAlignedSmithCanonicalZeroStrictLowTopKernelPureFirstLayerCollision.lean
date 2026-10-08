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

/-- If a polynomial family has zero special fibre, its entire first
positive parameter power divides it.  The existing exact-collision covariance
of `commonParameterFactorFamily` therefore applies directly to the canonical
first-actual quotient, without an independent cancellation argument. -/
theorem firstActualDeformationFamily_exactCollision_of_zeroSpecialFiber
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (hpositive : HasPositiveActualParameterLayer F)
    (hzero : polynomialFamilySpecialFiber F = 0)
    (a b : Fin 4 → Polynomial K)
    (hcollision : HasPolynomialFamilyExactGradientCollision F a b) :
    HasPolynomialFamilyExactGradientCollision
      (firstActualDeformationFamily F hpositive) a b := by
  have hrem : positiveParameterRemainder F = F := by
    unfold positiveParameterRemainder
    rw [hzero]
    simp [constantPolynomialFamily]
  have hcollRem :
      HasPolynomialFamilyExactGradientCollision
        (positiveParameterRemainder F) a b := by
    simpa [hrem] using hcollision
  exact
    polynomialFamilyExactGradientCollision_commonParameterFactor
      (firstPositiveActualParameterOrder F hpositive)
      (positiveParameterRemainder F)
      (positiveParameterRemainder_hasCommonParameterFactor_firstActual F hpositive)
      a b hcollRem

/-- Exact four-variable Hessian clock after removing the earliest positive
parameter power from a zero-special-fibre family.  This reuses the already
proved arbitrary-power common-factor determinant law. -/
theorem firstActualDeformationFamily_hasHessianDefect_of_zeroSpecialFiber
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (hpositive : HasPositiveActualParameterLayer F)
    (hzero : polynomialFamilySpecialFiber F = 0)
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) F Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (firstActualDeformationFamily F hpositive)
      (Delta - 4 * firstPositiveActualParameterOrder F hpositive) := by
  have hrem : positiveParameterRemainder F = F := by
    unfold positiveParameterRemainder
    rw [hzero]
    simp [constantPolynomialFamily]
  have hdefRem :
      HasPolynomialFamilyHessianDefect (K := K)
        (positiveParameterRemainder F) Delta := by
    simpa [hrem] using hdef
  exact
    commonParameterFactor_hasHessianDefect_sub_four_mul
      (K := K)
      (firstPositiveActualParameterOrder F hpositive)
      (positiveParameterRemainder F)
      (positiveParameterRemainder_hasCommonParameterFactor_firstActual F hpositive)
      Delta hdefRem


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

/-- The pure top-face case admits an *honest strict Hessian-clock
descent* on the collision-bearing first-actual quotient: writing
`r = D - j`, the quotient has exact determinant clock `4r-6`
rather than `4D-6`, and `2 ≤ r < D`.

This preserves the full polynomial family, not merely its first coefficient.
A separate restart adapter is still required to turn this clock decrease
into global HC4 repair progress. -/
theorem pureLongitudinal_firstActualQuotient_reducedClock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    let j := T.topKernelMarkedAxisFirstActualLayerOrder
    let r := T.topFace.degree - j
    HasPolynomialFamilyHessianDefect (K := K)
      (firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer)
      (4 * r - 6) ∧
      0 < 4 * r - 6 ∧
      4 * r - 6 < 4 * T.topFace.degree - 6 := by
  let F := T.topKernelMarkedAxisFirstContactFamily
  let hp := T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
  let j := T.topKernelMarkedAxisFirstActualLayerOrder
  let r := T.topFace.degree - j
  have hzero : polynomialFamilySpecialFiber F = 0 :=
    P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq
  have hdef :
      HasPolynomialFamilyHessianDefect (K := K)
        F (4 * T.topFace.degree - 6) := by
    simpa [F, topKernelOrdinaryReesDefect] using
      T.topKernelMarkedAxisFirstContact_hasHessianDefect
  have hquot :=
    firstActualDeformationFamily_hasHessianDefect_of_zeroSpecialFiber
      F hp hzero (4 * T.topFace.degree - 6) hdef
  have hjle :=
    P.pureLongitudinal_markedAxis_firstActualLayerOrder_le_degree_sub_two
      coefficient_ne_zero topFace_eq
  have hjpos := T.topKernelMarkedAxisFirstActualLayerOrder_pos
  have hD := T.topFace.degree_ge_three
  have harith :
      (4 * T.topFace.degree - 6) - 4 * j = 4 * r - 6 := by
    dsimp [j, r]
    omega
  have hclock :
      HasPolynomialFamilyHessianDefect (K := K)
        (firstActualDeformationFamily F hp)
        (4 * r - 6) := by
    change HasPolynomialFamilyHessianDefect (K := K)
      (firstActualDeformationFamily F hp)
      ((4 * T.topFace.degree - 6) - 4 * j) at hquot
    rw [harith] at hquot
    exact hquot
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact hclock
  · dsimp [r, j]
    omega
  · dsimp [r, j]
    omega

/-- The same reduced-clock quotient retains the two distinct constant
marked collision points throughout the parameter family. -/
theorem pureLongitudinal_firstActualQuotient_exactCollision
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree) :
    HasPolynomialFamilyExactGradientCollision
      (firstActualDeformationFamily
        T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer)
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) :=
  firstActualDeformationFamily_exactCollision_of_zeroSpecialFiber
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer
    (P.pureLongitudinal_markedAxis_specialFiber_eq_zero
      coefficient_ne_zero topFace_eq)
    (zeroPolynomialSection (K := K))
    (polynomialConstantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4)))
    T.topKernelMarkedAxisFirstContact_exactGradientCollision

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
