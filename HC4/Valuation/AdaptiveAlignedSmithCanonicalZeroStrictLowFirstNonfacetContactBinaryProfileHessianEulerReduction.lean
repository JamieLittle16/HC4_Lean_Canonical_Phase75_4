import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianFamily
import Mathlib.Tactic

/-!
# A19.R18: Euler reduction of the binary profile-Hessian determinant

The binary homogenized contact family satisfies the literal two-variable
weighted Euler equation in the family parameter and longitudinal source
coordinate.  Its falling row identities therefore remove the auxiliary
parameter-Hessian entries from the final binary determinant.

Writing

* `H00 = tau^2 d_tau^2 F`,
* `H01 = tau d_tau (E_0 F)`,
* `H11 = (E_0^2-E_0) F`,

we first obtain the division-free identity

    H00 * H11 - H01^2
      = (D-1) (tau d_tau F) * H11
          - (D-r) (E_0 F) * H01.

Using the first weighted Euler equation and the longitudinal falling row once
more gives a second form containing only `F`, `E_0 F`, and `H11`.  These are
the forms matched by the final weighted-source Schur calculation.

No new support, geometry, localization, or pivot-cancellation hypothesis is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 binary profile determinant Euler reduction.** -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily_eq_euler_reduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    P.binaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C ((T.topFace.degree : K) - 1)) *
        familyParameterEuler P.binaryHomogenizedFamily *
          P.binaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) - (P.profileWeight : K))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily *
          P.binaryProfileHessian01Family := by
  have hParameter := P.binaryHomogenized_fallingParameterRow
  have hLongitudinal := P.binaryHomogenized_fallingLongitudinalRow
  unfold QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily
    QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian00Family
    QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian01Family
    QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian11Family
  linear_combination
    hParameter *
      (HC4.Polynomial.eulerScaledHessian
        P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)) -
    hLongitudinal *
      (familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily))

/-- **R18 source-facing binary profile determinant form.**  Eliminating the
parameter Euler direction as well leaves only the binary family itself, its
longitudinal Euler derivative, and the longitudinal falling Hessian. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily_eq_longitudinal_reduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    P.binaryProfileHessianDetFamily =
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1))) *
        P.binaryHomogenizedFamily * P.binaryProfileHessian11Family +
      MvPolynomial.C
          (Polynomial.C
            ((P.profileWeight : K) * (1 - (P.profileWeight : K)))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily *
          P.binaryProfileHessian11Family -
      MvPolynomial.C
          (Polynomial.C
            (((T.topFace.degree : K) - (P.profileWeight : K)) ^ 2)) *
        HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily *
          HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily := by
  rw [P.binaryProfileHessianDetFamily_eq_euler_reduction]
  have hWeighted := P.binaryHomogenized_weightedEuler
  have hLongitudinal := P.binaryHomogenized_fallingLongitudinalRow
  unfold QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian01Family
    QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian11Family
  linear_combination
    MvPolynomial.C
        (Polynomial.C ((T.topFace.degree : K) - 1)) *
      hWeighted *
        (HC4.Polynomial.eulerScaledHessian
          P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)) -
    MvPolynomial.C
        (Polynomial.C
          ((T.topFace.degree : K) - (P.profileWeight : K))) *
      hLongitudinal *
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
