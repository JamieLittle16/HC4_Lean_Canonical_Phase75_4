import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianFamily
import Mathlib.Tactic

/-!
# A19.R18: extract the whole binary profile-Hessian determinant

The three whole-family profile-Hessian entries each carry one exact binary
parameter monomial `tau^(D-r*n)` on longitudinal degree `n`.  Their determinant
therefore carries the quadratic order `tau^(2D-r*n)`.  The only subtlety is
natural subtraction: for a nonzero convolution term both underlying raw
profile coefficients are nonzero, so `binary_profileOrder_add` supplies the
exact exponent addition.

This is the representation bridge needed by the final active-pivot
cancellation.  No Schur identity or new cancellation principle is introduced
here.
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

/-- Longitudinal degree `n` of the whole binary profile-Hessian determinant is
exactly the parameter monomial `tau^(2D-r*n)` times the integral profile
Hessian determinant coefficient. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessianDetFamily_longitudinal_coeff
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessianDetFamily).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (2 * T.topFace.degree - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (R.profileHessianDet.coeff n) := by
  have h0011 :
      (((MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian00Family) *
        (MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian11Family)).coeff n) =
        MvPolynomial.C
            ((Polynomial.X : Polynomial K) ^
              (2 * T.topFace.degree - P.profileWeight * n)) *
          MvPolynomial.map Polynomial.C
            ((R.profileHessian00 * R.profileHessian11).coeff n) := by
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [R.binaryProfileHessian00Family_longitudinal_coeff ij.1,
      R.binaryProfileHessian11Family_longitudinal_coeff ij.2]
    simp only [map_mul]
    by_cases hi : R.profile.coeff ij.1 = 0
    · have h00 : R.profileHessian00.coeff ij.1 = 0 := by
        rw [R.coeff_profileHessian00, hi]
        simp
      simp [h00]
    · by_cases hj : R.profile.coeff ij.2 = 0
      · have h11 : R.profileHessian11.coeff ij.2 = 0 := by
          rw [R.coeff_profileHessian11, hj]
          simp
        simp [h11]
      · have horder := R.binary_profileOrder_add hi hj
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [hsum] at horder
        have hC :
            MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.1)) *
              MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.2)) =
            (MvPolynomial.C
              ((Polynomial.X : Polynomial K) ^
                (2 * T.topFace.degree - P.profileWeight * n)) :
              MvPolynomial (Fin 3) (Polynomial K)) := by
          rw [← MvPolynomial.C_mul, ← pow_add, horder]
        calc
          (MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.1)) *
              MvPolynomial.map Polynomial.C
                (R.profileHessian00.coeff ij.1)) *
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.2)) *
                MvPolynomial.map Polynomial.C
                  (R.profileHessian11.coeff ij.2)) =
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.1)) *
                MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.2))) *
                (MvPolynomial.map Polynomial.C
                    (R.profileHessian00.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (R.profileHessian11.coeff ij.2)) := by ring
          _ = MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (2 * T.topFace.degree - P.profileWeight * n)) *
                (MvPolynomial.map Polynomial.C
                    (R.profileHessian00.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (R.profileHessian11.coeff ij.2)) := by rw [hC]

  have h0101 :
      (((MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian01Family) *
        (MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian01Family)).coeff n) =
        MvPolynomial.C
            ((Polynomial.X : Polynomial K) ^
              (2 * T.topFace.degree - P.profileWeight * n)) *
          MvPolynomial.map Polynomial.C
            ((R.profileHessian01 * R.profileHessian01).coeff n) := by
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [R.binaryProfileHessian01Family_longitudinal_coeff ij.1,
      R.binaryProfileHessian01Family_longitudinal_coeff ij.2]
    simp only [map_mul]
    by_cases hi : R.profile.coeff ij.1 = 0
    · have h01 : R.profileHessian01.coeff ij.1 = 0 := by
        rw [R.coeff_profileHessian01, hi]
        simp
      simp [h01]
    · by_cases hj : R.profile.coeff ij.2 = 0
      · have h01 : R.profileHessian01.coeff ij.2 = 0 := by
          rw [R.coeff_profileHessian01, hj]
          simp
        simp [h01]
      · have horder := R.binary_profileOrder_add hi hj
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [hsum] at horder
        have hC :
            MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.1)) *
              MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.2)) =
            (MvPolynomial.C
              ((Polynomial.X : Polynomial K) ^
                (2 * T.topFace.degree - P.profileWeight * n)) :
              MvPolynomial (Fin 3) (Polynomial K)) := by
          rw [← MvPolynomial.C_mul, ← pow_add, horder]
        calc
          (MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (T.topFace.degree - P.profileWeight * ij.1)) *
              MvPolynomial.map Polynomial.C
                (R.profileHessian01.coeff ij.1)) *
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.2)) *
                MvPolynomial.map Polynomial.C
                  (R.profileHessian01.coeff ij.2)) =
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.1)) *
                MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (T.topFace.degree - P.profileWeight * ij.2))) *
                (MvPolynomial.map Polynomial.C
                    (R.profileHessian01.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (R.profileHessian01.coeff ij.2)) := by ring
          _ = MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (2 * T.topFace.degree - P.profileWeight * n)) *
                (MvPolynomial.map Polynomial.C
                    (R.profileHessian01.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (R.profileHessian01.coeff ij.2)) := by rw [hC]

  rw [QsOtherFacetContactQuadraticReesPackage.binaryProfileHessianDetFamily]
  simp only [map_sub, map_mul, Polynomial.coeff_sub]
  rw [h0011, h0101]
  rw [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet,
    Polynomial.coeff_sub, map_sub]
  ring

/-- A zero binary family determinant layer at the exact quadratic profile order
forces the corresponding integral profile-Hessian determinant coefficient to
vanish. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ)
    (hzero :
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * T.topFace.degree - P.profileWeight * n) = 0) :
    R.profileHessianDet.coeff n = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  have hlong := R.binaryProfileHessianDetFamily_longitudinal_coeff n
  have hm := congrArg
    (fun A : MvPolynomial (Fin 3) (Polynomial K) => MvPolynomial.coeff m A)
    hlong
  rw [MvPolynomial.finSuccEquiv_coeff_coeff m
    P.binaryProfileHessianDetFamily n] at hm
  have hmN := congrArg
    (fun q : Polynomial K =>
      q.coeff (2 * T.topFace.degree - P.profileWeight * n)) hm
  rw [← familyParameterLayer_coeff] at hmN
  rw [hzero] at hmN
  simp only [MvPolynomial.coeff_zero] at hmN
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hmN
  have hrhs :
      (((Polynomial.X : Polynomial K) ^
          (2 * T.topFace.degree - P.profileWeight * n) *
        Polynomial.C (MvPolynomial.coeff m (R.profileHessianDet.coeff n))).coeff
          (2 * T.topFace.degree - P.profileWeight * n)) =
        MvPolynomial.coeff m (R.profileHessianDet.coeff n) := by
    simpa using
      (Polynomial.coeff_X_pow_mul
        (Polynomial.C (MvPolynomial.coeff m (R.profileHessianDet.coeff n)))
        (2 * T.topFace.degree - P.profileWeight * n) 0)
  rw [hrhs] at hmN
  exact hmN.symm

/-- If every exact quadratic profile layer of the whole binary Hessian
determinant vanishes, then the integral profile Hessian determinant is the zero
polynomial. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet_eq_zero_of_binaryFamily_layers
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (hlayers : ∀ n : ℕ,
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * T.topFace.degree - P.profileWeight * n) = 0) :
    R.profileHessianDet = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  exact R.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer n (hlayers n)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
