import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileHessianFamily
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryParameterEulerHessian
import Mathlib.Tactic

/-!
# A19 Euler reduction of the stationary profile-Hessian family

The stationary ramified family satisfies the exact weighted binary relation

    E_tau Q + r M Q = D Q,

where `M = n-E_0-E_1`, `r = stationaryWeight`, and
`D = r(n-1) = stationaryTotalDegree`.

Together with the falling parameter row this gives the two Hessian rows

    H00 + r H01 = (D-1) E_tau Q,
    H01 + r H11 = (D-r) M Q.

Consequently the stationary profile determinant admits the same source-facing
Euler reductions as the mature generic R18 binary profile determinant.  These
identities are denominator-free and keep the actual ramified source family
throughout.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

private theorem stationaryTotalDegree_cast
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R} :
    (F.stationaryTotalDegree : K) =
      (F.stationaryWeight : K) * ((F.highest.n : K) - 1) := by
  unfold QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree
  rw [Nat.cast_mul]
  have hn1 : 1 ≤ F.highest.n :=
    le_trans (by decide : 1 ≤ 2) F.highest.n_two_le
  rw [Nat.cast_sub hn1]
  norm_num

private theorem stationaryTotalDegree_mapped
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R} :
    MvPolynomial.C (Polynomial.C (F.stationaryTotalDegree : K)) =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
        (MvPolynomial.C (Polynomial.C (F.highest.n : K)) - 1) := by
  rw [stationaryTotalDegree_cast (K := K) (F := F)]
  simp only [map_mul, map_sub, map_one]

/-- Stationary depth commutes with parameter Euler differentiation. -/
theorem stationaryDepthEuler_familyParameterEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationaryDepthEuler (familyParameterEuler Q) =
      familyParameterEuler (D.stationaryDepthEuler Q) := by
  apply MvPolynomial.ext
  intro e
  rw [D.coeff_stationaryDepthEuler, coeff_familyParameterEuler,
    coeff_familyParameterEuler, D.coeff_stationaryDepthEuler]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add]
  ring

/-- Stationary depth is additive. -/
theorem stationaryDepthEuler_add
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (A B : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationaryDepthEuler (A + B) =
      D.stationaryDepthEuler A + D.stationaryDepthEuler B := by
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, D.coeff_stationaryDepthEuler]
  ring

/-- Stationary depth commutes with multiplication by a ground-field scalar. -/
theorem stationaryDepthEuler_groundScalar_mul
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (a : K)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationaryDepthEuler
        (MvPolynomial.C (Polynomial.C a) * Q) =
      MvPolynomial.C (Polynomial.C a) * D.stationaryDepthEuler Q := by
  apply MvPolynomial.ext
  intro e
  rw [D.coeff_stationaryDepthEuler, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul, D.coeff_stationaryDepthEuler]
  ring

/-- Iterating stationary depth equals its falling second iterate plus its first
iterate. -/
theorem stationaryDepthEuler_stationaryDepthEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationaryDepthEuler (D.stationaryDepthEuler Q) =
      D.stationaryDepthSecondEuler Q + D.stationaryDepthEuler Q := by
  unfold stationaryDepthSecondEuler
  ring

/-- Parameter Euler of stationary depth, expanded into the two source Euler
rows. -/
theorem familyParameterEuler_stationaryDepthEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterEuler (D.stationaryDepthEuler Q) =
      MvPolynomial.C (Polynomial.C (F.highest.n : K)) *
          familyParameterEuler Q -
        familyParameterEuler (HC4.Polynomial.mvEuler (0 : Fin 4) Q) -
        familyParameterEuler (HC4.Polynomial.mvEuler (1 : Fin 4) Q) := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_familyParameterEuler, D.coeff_stationaryDepthEuler,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_familyParameterEuler,
    coeff_familyParameterEuler, coeff_mvEuler, coeff_mvEuler]
  have h0 : (e 0 : Polynomial K) = Polynomial.C (e 0 : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) (e 0)).symm
  have h1 : (e 1 : Polynomial K) = Polynomial.C (e 1 : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) (e 1)).symm
  rw [h0, h1]
  have hC :
      Polynomial.C
          ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) =
        Polynomial.C (F.highest.n : K) -
          Polynomial.C (e 0 : K) - Polynomial.C (e 1 : K) := by
    rw [map_sub, map_sub]
  rw [hC]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add]
  ring

/-- **Stationary weighted binary Euler equation.** -/
theorem stationaryRamifiedFamily_parameterDepthWeightedEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterEuler D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          D.stationaryDepthEuler D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.stationaryTotalDegree : K)) *
        D.stationaryRamifiedFamily := by
  have h := D.stationaryRamifiedFamily_weightedEuler hthree houtThree
  have hD := stationaryTotalDegree_mapped (K := K) (F := F)
  unfold stationaryDepthEuler
  rw [hD]
  linear_combination h

/-- **Falling stationary depth row.** -/
theorem stationaryProfileHessian_depthRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessian01Family +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          D.stationaryProfileHessian11Family =
      MvPolynomial.C
          (Polynomial.C
            ((F.stationaryTotalDegree : K) - (F.stationaryWeight : K))) *
        D.stationaryDepthEuler D.stationaryRamifiedFamily := by
  have h := congrArg (D.stationaryDepthEuler)
    (D.stationaryRamifiedFamily_parameterDepthWeightedEuler hthree houtThree)
  rw [D.stationaryDepthEuler_add,
    D.stationaryDepthEuler_familyParameterEuler,
    D.stationaryDepthEuler_groundScalar_mul,
    D.stationaryDepthEuler_groundScalar_mul,
    D.stationaryDepthEuler_stationaryDepthEuler] at h
  unfold stationaryProfileHessian01Family stationaryProfileHessian11Family
  simp only [map_sub] at h ⊢
  linear_combination h

/-- **Falling stationary parameter row in profile-Hessian notation.** -/
theorem stationaryProfileHessian_parameterRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessian00Family +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          D.stationaryProfileHessian01Family =
      MvPolynomial.C
          (Polynomial.C ((F.stationaryTotalDegree : K) - 1)) *
        familyParameterEuler D.stationaryRamifiedFamily := by
  have hP := D.stationaryRamifiedFamily_fallingParameterRow hthree houtThree
  have hB := D.familyParameterEuler_stationaryDepthEuler
    D.stationaryRamifiedFamily
  have hD := stationaryTotalDegree_mapped (K := K) (F := F)
  unfold stationaryProfileHessian00Family stationaryProfileHessian01Family
  rw [hB, hD]
  simp only [map_add, map_sub, map_mul, map_one] at hP ⊢
  linear_combination hP

/-- **First Euler reduction of the stationary profile determinant.** -/
theorem stationaryProfileHessianDetFamily_eq_euler_reduction
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C ((F.stationaryTotalDegree : K) - 1)) *
        familyParameterEuler D.stationaryRamifiedFamily *
          D.stationaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            ((F.stationaryTotalDegree : K) - (F.stationaryWeight : K))) *
        D.stationaryDepthEuler D.stationaryRamifiedFamily *
          D.stationaryProfileHessian01Family := by
  have hp := D.stationaryProfileHessian_parameterRow hthree houtThree
  have hm := D.stationaryProfileHessian_depthRow hthree houtThree
  unfold stationaryProfileHessianDetFamily
  linear_combination
    hp * D.stationaryProfileHessian11Family -
    hm * D.stationaryProfileHessian01Family

/-- **Source-facing stationary determinant reduction.** -/
theorem stationaryProfileHessianDetFamily_eq_depth_reduction
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C
            ((F.stationaryTotalDegree : K) *
              ((F.stationaryTotalDegree : K) - 1))) *
        D.stationaryRamifiedFamily * D.stationaryProfileHessian11Family +
      MvPolynomial.C
          (Polynomial.C
            ((F.stationaryWeight : K) * (1 - (F.stationaryWeight : K)))) *
        D.stationaryDepthEuler D.stationaryRamifiedFamily *
          D.stationaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            (((F.stationaryTotalDegree : K) -
              (F.stationaryWeight : K)) ^ 2)) *
        D.stationaryDepthEuler D.stationaryRamifiedFamily *
          D.stationaryDepthEuler D.stationaryRamifiedFamily := by
  rw [D.stationaryProfileHessianDetFamily_eq_euler_reduction hthree houtThree]
  have hWeighted :=
    D.stationaryRamifiedFamily_parameterDepthWeightedEuler hthree houtThree
  have hDepth := D.stationaryProfileHessian_depthRow hthree houtThree
  have hWeighted' :
      familyParameterEuler D.stationaryRamifiedFamily =
        MvPolynomial.C (Polynomial.C (F.stationaryTotalDegree : K)) *
            D.stationaryRamifiedFamily -
          MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
            D.stationaryDepthEuler D.stationaryRamifiedFamily := by
    linear_combination hWeighted
  have hDepth' :
      familyParameterEuler
          (D.stationaryDepthEuler D.stationaryRamifiedFamily) =
        (MvPolynomial.C (Polynomial.C (F.stationaryTotalDegree : K)) -
            MvPolynomial.C (Polynomial.C (F.stationaryWeight : K))) *
            D.stationaryDepthEuler D.stationaryRamifiedFamily -
          MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
            D.stationaryDepthSecondEuler D.stationaryRamifiedFamily := by
    unfold stationaryProfileHessian01Family stationaryProfileHessian11Family at hDepth
    simp only [map_sub] at hDepth ⊢
    linear_combination hDepth
  unfold stationaryProfileHessian01Family stationaryProfileHessian11Family
  rw [hWeighted', hDepth']
  simp only [map_sub, map_mul, map_pow, map_one]
  ring

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
