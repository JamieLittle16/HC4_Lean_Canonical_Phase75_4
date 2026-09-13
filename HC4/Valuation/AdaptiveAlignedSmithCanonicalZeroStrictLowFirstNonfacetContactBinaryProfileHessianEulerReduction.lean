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
introduced.  The second identity is the source-facing normal form used by the
next Schur quotient adapter.
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
  simp only [map_sub, map_mul, map_pow, map_one] at hWeighted hLongitudinal ⊢
  linear_combination
    (MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) - 1) *
      hWeighted *
        (HC4.Polynomial.eulerScaledHessian
          P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)) -
    (MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) -
        MvPolynomial.C (Polynomial.C (P.profileWeight : K))) *
      hLongitudinal *
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)

/-- Longitudinal Euler differentiation commutes with the three transverse
unit inflations.  This is the missing one-row companion of the already-owned
Euler-Hessian transport theorem. -/
private theorem mvEuler_zero_unitTransverseInflateFamily
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.mvEuler (0 : Fin 4)
        (unitTransverseInflateFamily (K := K) F) =
      unitTransverseInflateFamily (K := K)
        (HC4.Polynomial.mvEuler (0 : Fin 4) F) := by
  ext d
  rw [coeff_mvEuler, coeff_unitTransverseInflateFamily,
    coeff_unitTransverseInflateFamily, coeff_mvEuler]
  ring_nf

/-- Contact-native preimage of the binary longitudinal profile determinant.
It uses only the contact family, its longitudinal Euler row, and its
longitudinal Euler-Hessian entry.  No Schur complement or active-pivot
cancellation is present in this definition. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.contactProfileHessianDetReduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.C
      (Polynomial.C
        ((T.topFace.degree : K) * ((T.topFace.degree : K) - 1))) *
    P.contactFamily *
      HC4.Polynomial.eulerScaledHessian
        P.contactFamily (0 : Fin 4) (0 : Fin 4) +
  MvPolynomial.C
      (Polynomial.C
        ((P.profileWeight : K) * (1 - (P.profileWeight : K)))) *
    HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily *
      HC4.Polynomial.eulerScaledHessian
        P.contactFamily (0 : Fin 4) (0 : Fin 4) -
  MvPolynomial.C
      (Polynomial.C
        (((T.topFace.degree : K) - (P.profileWeight : K)) ^ 2)) *
    HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily *
      HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily

/-- **R18.21 contact/binary profile bridge.**  The complete binary
profile-Hessian determinant is exactly simultaneous transverse inflation of
the contact-native longitudinal reduction.  This is the correct filtration
bridge for the final correction calculation: it preserves the contact
parameter grading and does not identify the contact and ray filtrations. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily_eq_map_contactProfileReduction
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    P.binaryProfileHessianDetFamily =
      unitTransverseInflateRingHom (K := K)
        P.contactProfileHessianDetReduction := by
  let f := unitTransverseInflateRingHom (K := K)
  change P.binaryProfileHessianDetFamily = f P.contactProfileHessianDetReduction
  have hfam :
      P.binaryHomogenizedFamily = f P.contactFamily := by
    rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily]
    exact (unitTransverseInflateRingHom_apply P.contactFamily).symm
  have hEuler :
      HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily =
        f (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) := by
    rw [hfam]
    rw [unitTransverseInflateRingHom_apply]
    exact mvEuler_zero_unitTransverseInflateFamily P.contactFamily
  have hHessian :
      P.binaryProfileHessian11Family =
        f (HC4.Polynomial.eulerScaledHessian
          P.contactFamily (0 : Fin 4) (0 : Fin 4)) := by
    unfold QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian11Family
    rw [hfam]
    rw [unitTransverseInflateRingHom_apply]
    exact eulerScaledHessian_unitTransverseInflateFamily
      P.contactFamily (0 : Fin 4) (0 : Fin 4)
  have hC (c : Polynomial K) :
      f (MvPolynomial.C c) =
        (MvPolynomial.C c : MvPolynomial (Fin 4) (Polynomial K)) := by
    dsimp [f]
    simp [unitTransverseInflateRingHom, kernelInflateHom_C]
  rw [P.binaryProfileHessianDetFamily_eq_longitudinal_reduction,
    hEuler, hHessian, hfam]
  unfold QsOtherFacetContactQuadraticReesPackage.contactProfileHessianDetReduction
  simp only [map_add, map_sub, map_mul]
  simp_rw [hC]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
