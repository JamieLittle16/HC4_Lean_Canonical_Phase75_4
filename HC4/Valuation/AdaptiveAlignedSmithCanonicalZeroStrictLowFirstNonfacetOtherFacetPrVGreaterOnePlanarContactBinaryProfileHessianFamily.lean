import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryProfileHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryParameterChainRule
import Mathlib.Tactic

/-!
# A19 whole-family binary Hessian profile of the singular planar carrier

The planar-contact binary homogenization has the exact pure grading

    tau-degree = D - (V+2)n.

This file lifts the integral carrier profile Hessian back to the honest
parameter family.  For the binary-homogenized planar family put

* `H00 = tau^2 d_tau^2 F`,
* `H01 = tau d_tau (E_0 F)`,
* `H11 = (E_0^2-E_0) F`.

Their longitudinal coefficient of degree `n` is exactly the single parameter
monomial `tau^(D-r*n)` multiplying the corresponding integral carrier-profile
coefficient, with `r = V+2`.  This is representation plumbing only: no Schur
cancellation, localization, or new geometric hypothesis occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem planarParameterEuler_X_pow_mul_C
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) =
      Polynomial.C (n : R) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Polynomial.derivative_mul, Polynomial.derivative_C]
      simp only [mul_zero, add_zero]
      rw [Polynomial.derivative_X_pow_succ]
      rw [pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem planarParameterSecondEuler_X_pow_mul_C
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a)) =
      Polynomial.C ((n : R) * ((n : R) - 1)) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_mul, Polynomial.derivative_C]
          simp only [mul_zero, add_zero]
          rw [Polynomial.derivative_X_pow_succ]
          rw [Polynomial.derivative_C_mul]
          rw [Polynomial.derivative_X_pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          have hscalar :
              (((n : R) + 1 + 1) * (((n : R) + 1 + 1) - 1)) =
                ((n : R) + 1 + 1) * ((n : R) + 1) := by
            ring
          rw [hscalar, map_mul]
          rw [pow_succ, pow_succ]
          ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- Parameter-parameter entry of the honest planar binary Hessian family. -/
noncomputable def binaryProfileHessian00Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterSecondEuler D.binaryHomogenizedFamily

/-- Mixed parameter/longitudinal entry of the honest planar binary Hessian
family. -/
noncomputable def binaryProfileHessian01Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  familyParameterEuler
    (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily)

/-- Longitudinal-longitudinal entry of the honest planar binary Hessian
family. -/
noncomputable def binaryProfileHessian11Family
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  HC4.Polynomial.eulerScaledHessian
    D.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)

/-- Determinant of the honest planar binary parameter/longitudinal Hessian
family. -/
noncomputable def binaryProfileHessianDetFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  D.binaryProfileHessian00Family * D.binaryProfileHessian11Family -
    D.binaryProfileHessian01Family * D.binaryProfileHessian01Family

/-- Every carrier monomial has enough binary parameter exponent. -/
theorem binaryProfileWeight_mul_longitudinal_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ P.carrier.support) :
    D.binaryProfileWeight * d (0 : Fin 4) ≤ T.topFace.degree := by
  have hbound := D.bound d hd
  rw [qsIntegralContactWeight_finsupp] at hbound
  have hordinary :
      HC4.Polynomial.ordinaryDegree4 d =
        d 0 + (d 1 + d 2 + d 3) := by
    simp [HC4.Polynomial.ordinaryDegree4]
    ring
  rw [hordinary] at hbound
  simp [binaryProfileWeight]
  omega

/-- Exact parameter-Euler eigenvalue of each planar binary-family source
coefficient. -/
theorem parameterEuler_coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d D.binaryHomogenizedFamily) =
      Polynomial.C
          ((T.topFace.degree : K) -
            (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d D.binaryHomogenizedFamily := by
  rw [D.coeff_binaryHomogenizedFamily]
  by_cases hd : d ∈ P.carrier.support
  · have hle := D.binaryProfileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - D.binaryProfileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [planarParameterEuler_X_pow_mul_C]
    rw [hcast]
  · have hcoeff : MvPolynomial.coeff d P.carrier = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hcoeff]

/-- Exact second falling parameter-Euler eigenvalue of each planar
binary-family source coefficient. -/
theorem parameterSecondEuler_coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          (MvPolynomial.coeff d D.binaryHomogenizedFamily)) =
      Polynomial.C
          (((T.topFace.degree : K) -
              (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K)) *
            ((T.topFace.degree : K) -
              (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K) - 1)) *
        MvPolynomial.coeff d D.binaryHomogenizedFamily := by
  rw [D.coeff_binaryHomogenizedFamily]
  by_cases hd : d ∈ P.carrier.support
  · have hle := D.binaryProfileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - D.binaryProfileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [planarParameterSecondEuler_X_pow_mul_C]
    rw [hcast]
  · have hcoeff : MvPolynomial.coeff d P.carrier = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [hcoeff]

/-- Exact mixed parameter/longitudinal Euler coefficient. -/
theorem parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d
          (HC4.Polynomial.mvEuler (0 : Fin 4) D.binaryHomogenizedFamily)) =
      (d (0 : Fin 4) : Polynomial K) *
        Polynomial.C
          ((T.topFace.degree : K) -
            (D.binaryProfileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d D.binaryHomogenizedFamily := by
  rw [coeff_mvEuler]
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.derivative_natCast, zero_mul, add_zero]
  rw [D.parameterEuler_coeff_binaryHomogenizedFamily d]
  ring

/-- Exact longitudinal falling-Euler Hessian coefficient. -/
theorem longitudinalEulerHessian_coeff_binaryHomogenizedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (HC4.Polynomial.eulerScaledHessian D.binaryHomogenizedFamily
          (0 : Fin 4) (0 : Fin 4)) =
      (d (0 : Fin 4) : Polynomial K) *
        ((d (0 : Fin 4) : Polynomial K) - 1) *
        MvPolynomial.coeff d D.binaryHomogenizedFamily := by
  rw [coeff_eulerScaledHessian]
  simp only [if_pos]
  ring

omit [IsAlgClosed K] in
private theorem carrierProfile_coeff_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (m : Fin 3 →₀ ℕ) (n : ℕ) :
    MvPolynomial.coeff m (D.carrierLongitudinalProfile.coeff n) =
      MvPolynomial.coeff (m.cons n) P.carrier := by
  simp [carrierLongitudinalProfile, MvPolynomial.finSuccEquiv_coeff_coeff]

/-- Whole-longitudinal coefficient formula for the parameter-parameter entry. -/
theorem binaryProfileHessian00Family_longitudinal_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      D.binaryProfileHessian00Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - D.binaryProfileWeight * n)) *
        MvPolynomial.map Polynomial.C (D.carrierProfileHessian00.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [binaryProfileHessian00Family]
  rw [coeff_familyParameterSecondEuler]
  rw [D.parameterSecondEuler_coeff_binaryHomogenizedFamily]
  rw [D.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := D.carrierProfile_coeff_coeff m n
  have haffine :
      (T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) =
        MvPolynomial.C
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K)) := by
    have hD :
        (T.topFace.degree : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (T.topFace.degree : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        T.topFace.degree).symm
    have hr :
        (D.binaryProfileWeight : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (D.binaryProfileWeight : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        D.binaryProfileWeight).symm
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hD, hr, hn, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub]
  have hscalar :
      ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) - 1) =
      MvPolynomial.C
        (((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K)) *
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K) - 1)) := by
    rw [haffine, ← MvPolynomial.C_1, ← MvPolynomial.C_sub,
      ← MvPolynomial.C_mul]
  have hprofile :
      MvPolynomial.coeff m (D.carrierProfileHessian00.coeff n) =
        (((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K)) *
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K) - 1)) *
          MvPolynomial.coeff m (D.carrierLongitudinalProfile.coeff n) := by
    rw [D.coeff_carrierProfileHessian00, hscalar, MvPolynomial.coeff_C_mul]
  rw [hprofile, hbase]
  simp only [Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_1]
  ring

/-- Whole-longitudinal coefficient formula for the mixed entry. -/
theorem binaryProfileHessian01Family_longitudinal_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      D.binaryProfileHessian01Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - D.binaryProfileWeight * n)) *
        MvPolynomial.map Polynomial.C (D.carrierProfileHessian01.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [binaryProfileHessian01Family]
  rw [coeff_familyParameterEuler]
  rw [D.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily]
  rw [D.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := D.carrierProfile_coeff_coeff m n
  have haffine :
      (T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K) =
        MvPolynomial.C
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K)) := by
    have hD :
        (T.topFace.degree : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (T.topFace.degree : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        T.topFace.degree).symm
    have hr :
        (D.binaryProfileWeight : MvPolynomial (Fin 3) K) =
          MvPolynomial.C (D.binaryProfileWeight : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
        D.binaryProfileWeight).symm
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [hD, hr, hn, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub]
  have hscalar :
      (n : MvPolynomial (Fin 3) K) *
        ((T.topFace.degree : MvPolynomial (Fin 3) K) -
          (D.binaryProfileWeight : MvPolynomial (Fin 3) K) *
            (n : MvPolynomial (Fin 3) K)) =
      MvPolynomial.C
        ((n : K) *
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K))) := by
    have hn :
        (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) :=
      (map_natCast
        (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) n).symm
    rw [haffine, hn, ← MvPolynomial.C_mul]
  have hprofile :
      MvPolynomial.coeff m (D.carrierProfileHessian01.coeff n) =
        ((n : K) *
          ((T.topFace.degree : K) - (D.binaryProfileWeight : K) * (n : K))) *
          MvPolynomial.coeff m (D.carrierLongitudinalProfile.coeff n) := by
    rw [D.coeff_carrierProfileHessian01, hscalar, MvPolynomial.coeff_C_mul]
  have hnPolynomial :
      (n : Polynomial K) = Polynomial.C (n : K) :=
    (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
  rw [hnPolynomial, hprofile, hbase]
  simp only [Polynomial.C_mul]
  ring

/-- Whole-longitudinal coefficient formula for the longitudinal entry. -/
theorem binaryProfileHessian11Family_longitudinal_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      D.binaryProfileHessian11Family).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (T.topFace.degree - D.binaryProfileWeight * n)) *
        MvPolynomial.map Polynomial.C (D.carrierProfileHessian11.coeff n) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [binaryProfileHessian11Family]
  rw [D.longitudinalEulerHessian_coeff_binaryHomogenizedFamily]
  rw [D.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  simp only [Finsupp.cons_zero]
  have hbase := D.carrierProfile_coeff_coeff m n
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
      MvPolynomial.coeff m (D.carrierProfileHessian11.coeff n) =
        ((n : K) * ((n : K) - 1)) *
          MvPolynomial.coeff m (D.carrierLongitudinalProfile.coeff n) := by
    rw [D.coeff_carrierProfileHessian11, hscalar, MvPolynomial.coeff_C_mul]
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

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
