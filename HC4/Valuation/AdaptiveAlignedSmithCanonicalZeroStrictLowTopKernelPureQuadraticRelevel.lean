import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPureDegreeCapObstruction
import Mathlib.Tactic

/-!
# Exact three-layer normal form at a reachable quadratic pure E3 relevel

If the first positive marked-axis order is j = D-2, the reduced whole-family
reverse-Rees potential is supported in parameter orders precisely 0, 1, 2.
The three parameter layers are the exact transverse weight-2, weight-1, and
weight-0 components of the UNCHANGED determinant-one represented source.

All higher parameter layers vanish.  The Hessian determinant of the whole
family is tau^2 and the literal marked gradient collision is preserved.
This is an explicit finite family-level normal form, not a terminal closing
assumption and not a fake ordinary-degree reduction.
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

/-- **Exact source-honest quadratic quotient.**

The source F remains the original represented determinant-one source. At
transverse cap two its reverse-Rees family consists of exactly three
coefficient layers, carries the exact tau^2 Hessian clock, and has the same
constant marked collision as the original represented source. -/
theorem pureLongitudinal_quadraticRelevel_threeLayers
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {coefficient : K}
    (coefficient_ne_zero : coefficient ≠ 0)
    (topFace_eq :
      T.topFace.face =
        MvPolynomial.C coefficient *
          (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
        T.topKernelReesSource :=
      by
        simpa [hr] using
          P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
            coefficient_ne_zero topFace_eq
    let Q :=
      reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        2 T.topKernelReesSource hbound
    (∀ n : ℕ, 2 < n → familyParameterLayer Q n = 0) ∧
      familyParameterLayer Q 0 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (2 : ℤ) T.topKernelReesSource ∧
      familyParameterLayer Q 1 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (1 : ℤ) T.topKernelReesSource ∧
      familyParameterLayer Q 2 =
        HC4.Polynomial.initialForm
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          (0 : ℤ) T.topKernelReesSource ∧
      HasPolynomialFamilyHessianDefect (K := K) Q 2 ∧
      HasPolynomialFamilyExactGradientCollision Q
        (zeroPolynomialSection (K := K))
        (polynomialConstantSection
          (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
  let hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2
      T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        coefficient_ne_zero topFace_eq
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    2 T.topKernelReesSource hbound
  have hQ :
      firstActualDeformationFamily T.topKernelMarkedAxisFirstContactFamily
        T.topKernelMarkedAxisFirstContact_hasPositiveActualLayer = Q := by
    have heq :=
      P.pureLongitudinal_firstActualQuotient_eq_relevelledReverseRees
        coefficient_ne_zero topFace_eq
    simpa [Q, hbound, hr] using heq
  have hclock : HasPolynomialFamilyHessianDefect (K := K) Q 2 := by
    have h := (P.pureLongitudinal_firstActualQuotient_reducedClock
      coefficient_ne_zero topFace_eq).1
    rw [hQ] at h
    simpa [hr] using h
  have hcoll : HasPolynomialFamilyExactGradientCollision Q
      (zeroPolynomialSection (K := K))
      (polynomialConstantSection
        (coordinateAxisPoint (K := K) (0 : Fin 4))) := by
    have h := P.pureLongitudinal_firstActualQuotient_exactCollision
      coefficient_ne_zero topFace_eq
    rwa [hQ] at h
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, hclock, hcoll⟩
  · intro n hn
    exact reverseWeightedReesFamily_parameterLayer_eq_zero_of_level_lt
      topKernelMarkedAxisNatWeight 2 n
      T.topKernelReesSource hbound hn
  · simpa [Q] using
      (reverseWeightedReesFamily_parameterLayer_eq_initialForm
        topKernelMarkedAxisNatWeight 2 0
        T.topKernelReesSource hbound (by omega))
  · simpa [Q] using
      (reverseWeightedReesFamily_parameterLayer_eq_initialForm
        topKernelMarkedAxisNatWeight 2 1
        T.topKernelReesSource hbound (by omega))
  · simpa [Q] using
      (reverseWeightedReesFamily_parameterLayer_eq_initialForm
        topKernelMarkedAxisNatWeight 2 2
        T.topKernelReesSource hbound (by omega))

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
