import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryCarrierEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreStaircaseProfileHessian
import Mathlib.Tactic

/-!
# A19 stationary parameter/depth Hessian family

The stationary outer index is the literal pair-depth

    m = n - (e₀ + e₁).

On the denominator-cleared ramified contact family this index is read by the
source operator

    M = n - E₀ - E₁.

This file packages that operator, its falling second iterate, and the three
honest family-level Hessian entries

    H00 = Eτ(Eτ-1) Q,
    H01 = Eτ M Q,
    H11 = M(M-1) Q.

Coefficientwise, `M` and `M(M-1)` multiply a source monomial by the expected
affine depth and falling affine depth.  These are the exact whole-family
objects whose determinant is to be identified with the cleared active Schur
quotient in the final stationary adapter.
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

/-- The source operator whose eigenvalue on a carrier monomial is the
stationary pair-depth `n-(e₀+e₁)`. -/
noncomputable def stationaryDepthEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.C (Polynomial.C (F.highest.n : K)) * Q -
    HC4.Polynomial.mvEuler (0 : Fin 4) Q -
    HC4.Polynomial.mvEuler (1 : Fin 4) Q

/-- Coefficientwise form of the stationary depth operator. -/
theorem coeff_stationaryDepthEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (e : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff e (D.stationaryDepthEuler Q) =
      Polynomial.C
          ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) *
        MvPolynomial.coeff e Q := by
  rw [stationaryDepthEuler, MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul, coeff_mvEuler, coeff_mvEuler]
  have h0 : (e 0 : Polynomial K) = Polynomial.C (e 0 : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) (e 0)).symm
  have h1 : (e 1 : Polynomial K) = Polynomial.C (e 1 : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) (e 1)).symm
  rw [h0, h1]
  rw [← Polynomial.C_sub, ← Polynomial.C_sub]
  ring

/-- Falling second stationary-depth operator `M(M-1)`. -/
noncomputable def stationaryDepthSecondEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  D.stationaryDepthEuler (D.stationaryDepthEuler Q) -
    D.stationaryDepthEuler Q

/-- Coefficientwise falling-depth formula. -/
theorem coeff_stationaryDepthSecondEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (e : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff e (D.stationaryDepthSecondEuler Q) =
      Polynomial.C
          ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) *
        (Polynomial.C
            ((F.highest.n : K) - (e 0 : K) - (e 1 : K)) - 1) *
        MvPolynomial.coeff e Q := by
  rw [stationaryDepthSecondEuler, MvPolynomial.coeff_sub,
    D.coeff_stationaryDepthEuler, D.coeff_stationaryDepthEuler,
    D.coeff_stationaryDepthEuler]
  ring

/-- Parameter-parameter entry of the honest stationary family Hessian. -/
noncomputable def stationaryProfileHessian00Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterSecondEuler D.stationaryRamifiedFamily

/-- Mixed parameter/depth entry of the honest stationary family Hessian. -/
noncomputable def stationaryProfileHessian01Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterEuler
    (D.stationaryDepthEuler D.stationaryRamifiedFamily)

/-- Depth-depth entry of the honest stationary family Hessian. -/
noncomputable def stationaryProfileHessian11Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  D.stationaryDepthSecondEuler D.stationaryRamifiedFamily

/-- Determinant of the honest stationary parameter/depth Hessian family. -/
noncomputable def stationaryProfileHessianDetFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  D.stationaryProfileHessian00Family * D.stationaryProfileHessian11Family -
    D.stationaryProfileHessian01Family * D.stationaryProfileHessian01Family

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
