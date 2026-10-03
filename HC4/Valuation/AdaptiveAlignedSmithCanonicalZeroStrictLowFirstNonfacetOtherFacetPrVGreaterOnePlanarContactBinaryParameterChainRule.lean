import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryProfileHessianFamily
import Mathlib.Tactic

/-!
# A19 planar binary parameter chain rule

The source-honest planar-contact binary homogenization has the exact pure
weight

    tau-degree + (V+2) * d₀ = D.

The preceding whole-family Hessian module already proves the coefficientwise
parameter, mixed and longitudinal Euler eigenvalue formulas.  This file
packages those formulas into the three division-free whole-family identities
consumed by the Euler/Schur straightening:

    E_tau F + r E_0 F = D F,

    F_tau_tau + r F_tau,0 = (D-1) E_tau F,

    F_tau,0 + r F_00 = (D-r) E_0 F.

Here the second derivatives are the falling Euler-scaled derivatives used by
the existing stationary profile machinery.  No support hypothesis, pivot
cancellation, localization, or auxiliary clock is added.
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

/-- **Planar binary weighted Euler equation.**  After simultaneous transverse
inflation all transverse contact weight has moved into the family parameter,
leaving the literal binary weight `(1, V+2)` on `(tau,x₀)`. -/
theorem binaryHomogenized_weightedEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    familyParameterEuler D.binaryHomogenizedFamily +
        MvPolynomial.C (Polynomial.C (D.binaryProfileWeight : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily =
      MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) *
        D.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_mvEuler]
  rw [D.parameterEuler_coeff_binaryHomogenizedFamily d]
  simp only [map_sub, map_mul, map_natCast]
  ring

/-- **Planar binary falling parameter row.**  Differentiating the binary
weighted Euler equation in the family parameter gives the relation between
`H00` and `H01` used by the profile Hessian. -/
theorem binaryHomogenized_fallingParameterRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    familyParameterSecondEuler D.binaryHomogenizedFamily +
        MvPolynomial.C (Polynomial.C (D.binaryProfileWeight : K)) *
          familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily) =
      MvPolynomial.C
          (Polynomial.C ((T.topFace.degree : K) - 1)) *
        familyParameterEuler D.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterSecondEuler, coeff_familyParameterEuler]
  rw [D.parameterSecondEuler_coeff_binaryHomogenizedFamily d]
  rw [D.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily d]
  rw [D.parameterEuler_coeff_binaryHomogenizedFamily d]
  simp only [map_sub, map_mul, map_natCast, map_one]
  ring

/-- **Planar binary falling longitudinal row.**  Differentiating in `x₀`
gives the mixed/longitudinal relation of the canonical binary profile Hessian. -/
theorem binaryHomogenized_fallingLongitudinalRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily) +
        MvPolynomial.C (Polynomial.C (D.binaryProfileWeight : K)) *
          HC4.Polynomial.eulerScaledHessian
            D.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4) =
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) - (D.binaryProfileWeight : K))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler]
  rw [D.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily d]
  rw [D.longitudinalEulerHessian_coeff_binaryHomogenizedFamily d]
  simp only [coeff_mvEuler, map_sub, map_add, map_mul, map_pow,
    map_natCast, map_one]
  ring

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
