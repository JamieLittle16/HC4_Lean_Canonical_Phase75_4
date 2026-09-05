import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryParameterChainRule
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianRecognition
import Mathlib.Tactic

/-!
# A19.R18: whole-family binary profile Hessian

The layer-recognition lemmas identify the three staircase Hessian coefficients
at their exact parameter orders.  For the final determinant convolution it is
more convenient to package the corresponding whole source families first.

For the binary-homogenized contact family put

* `H00 = tau^2 d_tau^2 F`,
* `H01 = tau d_tau (E_0 F)`,
* `H11 = (E_0^2-E_0) F`.

Their longitudinal coefficient of degree `n` is exactly the single parameter
monomial `tau^(D-r*n)` multiplying the integral profile-Hessian coefficient of
the same degree.  No Schur or pivot cancellation occurs in this module.
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

/-- Parameter-parameter entry of the honest binary Hessian family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian00Family
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterSecondEuler P.binaryHomogenizedFamily

/-- Mixed parameter/longitudinal entry of the honest binary Hessian family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian01Family
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterEuler
    (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)

/-- Longitudinal-longitudinal entry of the honest binary Hessian family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian11Family
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  HC4.Polynomial.eulerScaledHessian
    P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)

/-- Determinant of the honest binary parameter/longitudinal Hessian family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  P.binaryProfileHessian00Family * P.binaryProfileHessian11Family -
    P.binaryProfileHessian01Family * P.binaryProfileHessian01Family

omit [IsAlgClosed K] in
private theorem QsOtherFacetContactRawLongitudinalProfilePackage.profile_coeff_coeff
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (m : Fin 3 →₀ ℕ) (n : ℕ) :
    MvPolynomial.coeff m (R.profile.coeff n) =
      MvPolynomial.coeff (m.cons n)
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [R.profile_eq, qsContactRawLongitudinalProfile]
  exact MvPolynomial.finSuccEquiv_coeff_coeff m
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) n

/-- Whole-longitudinal coefficient formula for the parameter-parameter entry. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessian00Family_longitudinal_coeff
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian00Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (R.profileHessian00.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian00Family]
  rw [coeff_familyParameterSecondEuler]
  rw [P.parameterSecondEuler_coeff_binaryHomogenizedFamily]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := R.profile_coeff_coeff m n
  have haffine :
      (T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) =
        MvPolynomial.C
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K)) := by
    have hD :
        (T.topFace.degree : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (T.topFace.degree : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        T.topFace.degree).symm
    have hr :
        (P.profileWeight : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (P.profileWeight : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        P.profileWeight).symm
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hD, hr, hn, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub]
  have hscalar :
      ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) - 1) =
      MvPolynomial.C
        (((T.topFace.degree : K) - (P.profileWeight : K) * (n : K)) *
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K) - 1)) := by
    rw [haffine, ← MvPolynomial.C_1, ← MvPolynomial.C_sub,
      ← MvPolynomial.C_mul]
  have hprofile :
      MvPolynomial.coeff m (R.profileHessian00.coeff n) =
        (((T.topFace.degree : K) - (P.profileWeight : K) * (n : K)) *
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K) - 1)) *
          MvPolynomial.coeff m (R.profile.coeff n) := by
    rw [R.coeff_profileHessian00, hscalar, MvPolynomial.coeff_C_mul]
  rw [hprofile, hbase]
  simp only [Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_1]
  ring

/-- Whole-longitudinal coefficient formula for the mixed entry. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessian01Family_longitudinal_coeff
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian01Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (R.profileHessian01.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian01Family]
  rw [coeff_familyParameterEuler]
  rw [P.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := R.profile_coeff_coeff m n
  have haffine :
      (T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) =
        MvPolynomial.C
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K)) := by
    have hD :
        (T.topFace.degree : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (T.topFace.degree : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        T.topFace.degree).symm
    have hr :
        (P.profileWeight : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (P.profileWeight : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        P.profileWeight).symm
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hD, hr, hn, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub]
  have hscalar :
      (n : MvPolynomial (Fin 3) K) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) =
      MvPolynomial.C
        ((n : K) *
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K))) := by
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [haffine, hn, ← MvPolynomial.C_mul]
  have hprofile :
      MvPolynomial.coeff m (R.profileHessian01.coeff n) =
        ((n : K) *
          ((T.topFace.degree : K) - (P.profileWeight : K) * (n : K))) *
          MvPolynomial.coeff m (R.profile.coeff n) := by
    rw [R.coeff_profileHessian01, hscalar, MvPolynomial.coeff_C_mul]
  have hnPolynomial :
      (n : Polynomial K) = Polynomial.C (n : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
  rw [hnPolynomial, hprofile, hbase]
  simp only [Polynomial.C_mul]
  ring

/-- Whole-longitudinal coefficient formula for the longitudinal entry. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessian11Family_longitudinal_coeff
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian11Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (R.profileHessian11.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetContactQuadraticReesPackage.binaryProfileHessian11Family]
  rw [P.longitudinalEulerHessian_coeff_binaryHomogenizedFamily]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := R.profile_coeff_coeff m n
  have hscalar :
      (n : MvPolynomial (Fin 3) K) *
          ((n : MvPolynomial (Fin 3) K) - 1) =
        MvPolynomial.C ((n : K) * ((n : K) - 1)) := by
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hn, ← MvPolynomial.C_1, ← MvPolynomial.C_sub,
      ← MvPolynomial.C_mul]
  have hprofile :
      MvPolynomial.coeff m (R.profileHessian11.coeff n) =
        ((n : K) * ((n : K) - 1)) *
          MvPolynomial.coeff m (R.profile.coeff n) := by
    rw [R.coeff_profileHessian11, hscalar, MvPolynomial.coeff_C_mul]
  have hnPolynomial :
      (n : Polynomial K) * ((n : Polynomial K) - 1) =
        Polynomial.C ((n : K) * ((n : K) - 1)) := by
    have hn :
        (n : Polynomial K) = Polynomial.C (n : K) :=
      (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
    rw [hn, ← Polynomial.C_1, ← Polynomial.C_sub, ← Polynomial.C_mul]
  rw [hnPolynomial, hprofile, hbase]
  simp only [Polynomial.C_mul]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation