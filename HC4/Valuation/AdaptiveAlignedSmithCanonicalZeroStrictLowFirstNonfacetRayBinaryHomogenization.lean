import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayProfileRees
import HC4.Valuation.ExactKernelDefectDrop
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryLongitudinalHessianCoefficients
import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# A19.R18.19: ray-native binary homogenisation

The profile-ready ray Rees has source weight `W` and level `D`.  Inflate the
three transverse source coordinates by `tau^(W i)`.  This cancels the
transverse part of the reverse-Rees order, leaving the binary order

    D - W 0 * d 0.

Unlike the earlier contact construction, the parameter-zero layer before
inflation is exactly the locked affine ray.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem parameterEuler_X_pow_mul_C
    (n : ℕ) (a : K) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial K) ^ n * Polynomial.C a) =
      Polynomial.C (n : K) *
        ((Polynomial.X : Polynomial K) ^ n * Polynomial.C a) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Polynomial.derivative_mul, Polynomial.derivative_C,
        Polynomial.derivative_X_pow_succ]
      simp only [mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      ring

private theorem parameterSecondEuler_X_pow_mul_C
    (n : ℕ) (a : K) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          ((Polynomial.X : Polynomial K) ^ n * Polynomial.C a)) =
      Polynomial.C ((n : K) * ((n : K) - 1)) *
        ((Polynomial.X : Polynomial K) ^ n * Polynomial.C a) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_mul, Polynomial.derivative_C]
          simp only [mul_zero, add_zero]
          rw [Polynomial.derivative_mul, Polynomial.derivative_C]
          simp only [mul_zero, add_zero]
          rw [Polynomial.derivative_X_pow_succ]
          rw [Polynomial.derivative_C_mul]
          rw [Polynomial.derivative_X_pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          have hscalar :
              (((n : K) + 1 + 1) * (((n : K) + 1 + 1) - 1)) =
                ((n : K) + 1 + 1) * ((n : K) + 1) := by ring
          rw [hscalar, map_mul]
          rw [pow_succ, pow_succ]
          ring

/-- Inflate transverse coordinate `i` by the corresponding arbitrary natural
weight. -/
noncomputable def weightedTransverseInflateFamily
    (W : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  kernelInflateHom (K := K) (3 : Fin 4) (W 3)
    (kernelInflateHom (K := K) (2 : Fin 4) (W 2)
      (kernelInflateHom (K := K) (1 : Fin 4) (W 1) F))

/-- Exact coefficient multiplier for weighted transverse inflation. -/
theorem coeff_weightedTransverseInflateFamily
    (W : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (weightedTransverseInflateFamily (K := K) W F) =
      Polynomial.X ^ (W 1 * d 1 + W 2 * d 2 + W 3 * d 3) *
        MvPolynomial.coeff d F := by
  unfold weightedTransverseInflateFamily
  repeat' rw [coeff_kernelInflateHom]
  simp [kernelCoefficientTauPower]
  rw [pow_add, pow_add]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- The doubled ray reverse-Rees family owned by the profile package. -/
noncomputable def QsOtherFacetRayProfileReesPackage.rayFamily
    (P : QsOtherFacetRayProfileReesPackage C R) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily P.weight P.level
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) P.bound

/-- Ray-native binary homogenisation. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryHomogenizedFamily
    (P : QsOtherFacetRayProfileReesPackage C R) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  weightedTransverseInflateFamily (K := K) P.weight P.rayFamily

/-- Exact source coefficient of the ray-native binary family. -/
theorem QsOtherFacetRayProfileReesPackage.coeff_binaryHomogenizedFamily
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d P.binaryHomogenizedFamily =
      Polynomial.X ^ (P.level - P.profileWeight * d (0 : Fin 4)) *
        Polynomial.C
          (MvPolynomial.coeff d
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family)) := by
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  rw [QsOtherFacetRayProfileReesPackage.binaryHomogenizedFamily]
  rw [coeff_weightedTransverseInflateFamily]
  rw [QsOtherFacetRayProfileReesPackage.rayFamily]
  rw [reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ F.support
  · rw [if_pos hd]
    have hbound := P.bound d hd
    have hweight :
        Finsupp.weight P.weight d =
          P.weight 0 * d 0 + P.weight 1 * d 1 +
            P.weight 2 * d 2 + P.weight 3 * d 3 := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype]
      · rw [Fin.sum_univ_four]
        ring
      · intro i
        simp
    rw [hweight] at hbound
    have hbound' :
        P.weight 0 * d 0 +
            (P.weight 1 * d 1 + P.weight 2 * d 2 + P.weight 3 * d 3) ≤
          P.level := by
      omega
    rw [P.profileWeight_eq]
    rw [hweight]
    rw [← mul_assoc, ← pow_add]
    congr 1
    apply congrArg (fun n : ℕ => Polynomial.X ^ n)
    omega
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hd, hcoeff]

/-- Every represented source monomial has admissible longitudinal profile
order. -/
theorem QsOtherFacetRayProfileReesPackage.profileWeight_mul_longitudinal_le
    (P : QsOtherFacetRayProfileReesPackage C R)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support) :
    P.profileWeight * d (0 : Fin 4) ≤ P.level := by
  rw [P.profileWeight_eq]
  have hbound := P.bound d hd
  have hweight :
      Finsupp.weight P.weight d =
        P.weight 0 * d 0 + P.weight 1 * d 1 +
          P.weight 2 * d 2 + P.weight 3 * d 3 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · rw [Fin.sum_univ_four]
      ring
    · intro i
      simp
  rw [hweight] at hbound
  omega

/-- Exact parameter-Euler eigenvalue of each ray-binary source coefficient. -/
theorem QsOtherFacetRayProfileReesPackage.parameterEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d P.binaryHomogenizedFamily) =
      Polynomial.C
          ((P.level : K) - (P.profileWeight : K) * (d 0 : K)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((P.level - P.profileWeight * d 0 : ℕ) : K) =
          (P.level : K) - (P.profileWeight : K) * (d 0 : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [parameterEuler_X_pow_mul_C, hcast]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

/-- Exact second falling parameter-Euler eigenvalue. -/
theorem QsOtherFacetRayProfileReesPackage.parameterSecondEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          (MvPolynomial.coeff d P.binaryHomogenizedFamily)) =
      Polynomial.C
          (((P.level : K) - (P.profileWeight : K) * (d 0 : K)) *
            ((P.level : K) - (P.profileWeight : K) * (d 0 : K) - 1)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((P.level - P.profileWeight * d 0 : ℕ) : K) =
          (P.level : K) - (P.profileWeight : K) * (d 0 : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [parameterSecondEuler_X_pow_mul_C, hcast]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

/-- Mixed parameter/longitudinal Euler coefficient. -/
theorem QsOtherFacetRayProfileReesPackage.parameterEuler_longitudinalEuler_coeff
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d
          (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)) =
      (d 0 : Polynomial K) *
        Polynomial.C
          ((P.level : K) - (P.profileWeight : K) * (d 0 : K)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [coeff_mvEuler]
  simp only [Polynomial.derivative_mul]
  have hconst : Polynomial.derivative (d 0 : Polynomial K) = 0 := by simp
  rw [hconst, zero_mul, zero_add]
  calc
    Polynomial.X * ((d 0 : Polynomial K) *
        Polynomial.derivative (MvPolynomial.coeff d P.binaryHomogenizedFamily)) =
        (d 0 : Polynomial K) *
          (Polynomial.X * Polynomial.derivative
            (MvPolynomial.coeff d P.binaryHomogenizedFamily)) := by ring
    _ = (d 0 : Polynomial K) *
          (Polynomial.C
              ((P.level : K) - (P.profileWeight : K) * (d 0 : K)) *
            MvPolynomial.coeff d P.binaryHomogenizedFamily) := by
      rw [P.parameterEuler_coeff_binaryHomogenizedFamily d]
    _ = _ := by ring

/-- Pure longitudinal Euler-Hessian coefficient. -/
theorem QsOtherFacetRayProfileReesPackage.longitudinalEulerHessian_coeff
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (HC4.Polynomial.eulerScaledHessian P.binaryHomogenizedFamily
          (0 : Fin 4) 0) =
      ((d 0 : Polynomial K) * ((d 0 : Polynomial K) - 1)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [coeff_eulerScaledHessian]
  simp only [if_pos]
  ring

/-- Parameter-parameter entry of the ray-native profile Hessian. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryProfileHessian00Family
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  familyParameterSecondEuler P.binaryHomogenizedFamily

/-- Mixed parameter/longitudinal entry of the ray-native profile Hessian. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryProfileHessian01Family
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  familyParameterEuler
    (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)

/-- Longitudinal-longitudinal entry of the ray-native profile Hessian. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryProfileHessian11Family
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  HC4.Polynomial.eulerScaledHessian
    P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4)

/-- Determinant of the ray-native parameter/longitudinal Hessian. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryProfileHessianDetFamily
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  P.binaryProfileHessian00Family * P.binaryProfileHessian11Family -
    P.binaryProfileHessian01Family * P.binaryProfileHessian01Family

/-- Binary source weight: only the distinguished longitudinal coordinate is
retained after transverse inflation. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryInflationWeight
    (P : QsOtherFacetRayProfileReesPackage C R) : Fin 4 → ℕ :=
  fun i => if i = (0 : Fin 4) then P.profileWeight else 0

theorem QsOtherFacetRayProfileReesPackage.binaryInflationWeight_degree
    (P : QsOtherFacetRayProfileReesPackage C R)
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight P.binaryInflationWeight d =
      P.profileWeight * d (0 : Fin 4) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype] <;>
    simp [Fin.sum_univ_four,
      QsOtherFacetRayProfileReesPackage.binaryInflationWeight,
      nsmul_eq_mul, Nat.mul_comm]

/-- Hessian clock after transverse inflation.  The three transverse Hessian
inflation contributions cancel from the original ray clock. -/
def QsOtherFacetRayProfileReesPackage.binaryHessianClock
    (P : QsOtherFacetRayProfileReesPackage C R) : ℕ :=
  4 * P.level - 2 * P.profileWeight

/-- The ray package's quadratic margin survives binary normalization. -/
theorem QsOtherFacetRayProfileReesPackage.two_level_lt_binaryHessianClock
    (P : QsOtherFacetRayProfileReesPackage C R) :
    2 * P.level < P.binaryHessianClock := by
  have hsum :
      ∑ i : Fin 4, P.weight i =
        P.weight 0 + P.weight 1 + P.weight 2 + P.weight 3 := by
    rw [Fin.sum_univ_four]
  have hprofile := P.profileWeight_eq
  have h := P.two_level_lt_defect
  rw [hsum] at h
  unfold QsOtherFacetRayProfileReesPackage.binaryHessianClock
  rw [hprofile]
  omega

/-- Every quadratic profile order used downstream lies below the normalized
binary Hessian clock. -/
theorem QsOtherFacetRayProfileReesPackage.quadraticProfileOrder_lt_clock
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    2 * P.level - P.profileWeight * n < P.binaryHessianClock := by
  exact lt_of_le_of_lt (Nat.sub_le _ _) P.two_level_lt_binaryHessianClock

/-- Longitudinal polynomial view of the ray-native binary family. -/
noncomputable def QsOtherFacetRayProfileReesPackage.binaryHomogenizedLongitudinal
    (P : QsOtherFacetRayProfileReesPackage C R) :
    Polynomial (MvPolynomial (Fin 3) (Polynomial K)) :=
  MvPolynomial.finSuccEquiv (Polynomial K) 3 P.binaryHomogenizedFamily

/-- The unchanged represented source, viewed as a polynomial in its
longitudinal coordinate. -/
noncomputable def rayRawLongitudinalProfile :
    Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.finSuccEquiv K 3
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)

/-- Integral weighted parameter Euler of the unchanged source profile. -/
noncomputable def QsOtherFacetRayProfileReesPackage.profileParameterEuler
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  Polynomial.C (P.level : MvPolynomial (Fin 3) K) *
      (rayRawLongitudinalProfile (T := T)) -
    Polynomial.C (P.profileWeight : MvPolynomial (Fin 3) K) *
      HC4.Polynomial.eulerDerivative (rayRawLongitudinalProfile (T := T))

noncomputable def QsOtherFacetRayProfileReesPackage.profileHessian00
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  Polynomial.C ((P.level : MvPolynomial (Fin 3) K) - 1) *
      P.profileParameterEuler -
    Polynomial.C (P.profileWeight : MvPolynomial (Fin 3) K) *
      HC4.Polynomial.eulerDerivative P.profileParameterEuler

noncomputable def QsOtherFacetRayProfileReesPackage.profileHessian01
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  HC4.Polynomial.eulerDerivative P.profileParameterEuler

noncomputable def QsOtherFacetRayProfileReesPackage.profileHessian11
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  HC4.Polynomial.eulerDerivative
      (HC4.Polynomial.eulerDerivative (rayRawLongitudinalProfile (T := T))) -
    HC4.Polynomial.eulerDerivative (rayRawLongitudinalProfile (T := T))

noncomputable def QsOtherFacetRayProfileReesPackage.profileHessianDet
    (P : QsOtherFacetRayProfileReesPackage C R) :=
  P.profileHessian00 * P.profileHessian11 -
    P.profileHessian01 * P.profileHessian01

theorem QsOtherFacetRayProfileReesPackage.coeff_profileParameterEuler
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    P.profileParameterEuler.coeff n =
      ((P.level : MvPolynomial (Fin 3) K) -
        (P.profileWeight : MvPolynomial (Fin 3) K) * n) *
        (rayRawLongitudinalProfile (T := T)).coeff n := by
  simp [QsOtherFacetRayProfileReesPackage.profileParameterEuler,
    HC4.Polynomial.coeff_eulerDerivative]
  ring

theorem QsOtherFacetRayProfileReesPackage.coeff_profileHessian00
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    P.profileHessian00.coeff n =
      (((P.level : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) * n) *
        ((P.level : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) * n - 1)) *
        (rayRawLongitudinalProfile (T := T)).coeff n := by
  simp only [QsOtherFacetRayProfileReesPackage.profileHessian00,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    HC4.Polynomial.coeff_eulerDerivative]
  rw [P.coeff_profileParameterEuler]
  ring

theorem QsOtherFacetRayProfileReesPackage.coeff_profileHessian01
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    P.profileHessian01.coeff n =
      (n : MvPolynomial (Fin 3) K) *
        ((P.level : MvPolynomial (Fin 3) K) -
          (P.profileWeight : MvPolynomial (Fin 3) K) * n) *
        (rayRawLongitudinalProfile (T := T)).coeff n := by
  simp [QsOtherFacetRayProfileReesPackage.profileHessian01,
    HC4.Polynomial.coeff_eulerDerivative, P.coeff_profileParameterEuler]
  ring

theorem QsOtherFacetRayProfileReesPackage.coeff_profileHessian11
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    P.profileHessian11.coeff n =
      ((n : MvPolynomial (Fin 3) K) *
        ((n : MvPolynomial (Fin 3) K) - 1)) *
        (rayRawLongitudinalProfile (T := T)).coeff n := by
  simp [QsOtherFacetRayProfileReesPackage.profileHessian11,
    HC4.Polynomial.coeff_eulerDerivative]
  ring

/-- The longitudinal coefficient is the represented-source profile
coefficient times its unique ray-binary parameter monomial. -/
theorem QsOtherFacetRayProfileReesPackage.coeff_binaryHomogenizedLongitudinal
    (P : QsOtherFacetRayProfileReesPackage C R)
    (n : ℕ) :
    P.binaryHomogenizedLongitudinal.coeff n =
      MvPolynomial.C
          (Polynomial.X ^ (P.level - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C
          ((rayRawLongitudinalProfile (T := T)).coeff n) := by
  ext m
  rw [QsOtherFacetRayProfileReesPackage.binaryHomogenizedLongitudinal]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul]
  simp only [MvPolynomial.coeff_map]
  simp [rayRawLongitudinalProfile,
    MvPolynomial.finSuccEquiv_coeff_coeff]

private theorem coeff_rayRawLongitudinalProfile
    (m : Fin 3 →₀ ℕ) (n : ℕ) :
    MvPolynomial.coeff m ((rayRawLongitudinalProfile (T := T)).coeff n) =
      MvPolynomial.coeff (m.cons n)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) := by
  rw [rayRawLongitudinalProfile]
  exact MvPolynomial.finSuccEquiv_coeff_coeff m _ n

/-- Whole-longitudinal recognition of the parameter-parameter Hessian row. -/
theorem QsOtherFacetRayProfileReesPackage.binaryProfileHessian00_longitudinal_coeff
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian00Family).coeff n =
      MvPolynomial.C (Polynomial.X ^ (P.level - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (P.profileHessian00.coeff n) := by
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetRayProfileReesPackage.binaryProfileHessian00Family]
  rw [coeff_familyParameterSecondEuler]
  rw [P.parameterSecondEuler_coeff_binaryHomogenizedFamily]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  have hp : MvPolynomial.coeff m (P.profileHessian00.coeff n) =
      (((P.level : K) - (P.profileWeight : K) * (n : K)) *
        ((P.level : K) - (P.profileWeight : K) * (n : K) - 1)) *
        MvPolynomial.coeff (m.cons n)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) := by
    rw [P.coeff_profileHessian00]
    rw [show (n : MvPolynomial (Fin 3) K) = MvPolynomial.C (n : K) by norm_num]
    rw [show (P.level : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (P.level : K) by norm_num]
    rw [show (P.profileWeight : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (P.profileWeight : K) by norm_num]
    rw [← map_mul, ← map_sub]
    rw [show MvPolynomial.C
          ((P.level : K) - (P.profileWeight : K) * (n : K)) - 1 =
        MvPolynomial.C
          ((P.level : K) - (P.profileWeight : K) * (n : K) - 1) by
      change MvPolynomial.C _ - MvPolynomial.C 1 = _
      rw [← map_sub]]
    rw [← map_mul]
    rw [MvPolynomial.coeff_C_mul, coeff_rayRawLongitudinalProfile]
  simp only [Finsupp.cons_zero]
  rw [hp]
  apply congrArg (fun f : Polynomial K => f.coeff _)
  simp only [map_mul]
  ring

/-- Whole-longitudinal recognition of the mixed Hessian row. -/
theorem QsOtherFacetRayProfileReesPackage.binaryProfileHessian01_longitudinal_coeff
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian01Family).coeff n =
      MvPolynomial.C (Polynomial.X ^ (P.level - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (P.profileHessian01.coeff n) := by
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetRayProfileReesPackage.binaryProfileHessian01Family]
  rw [coeff_familyParameterEuler]
  rw [P.parameterEuler_longitudinalEuler_coeff]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  have hp : MvPolynomial.coeff m (P.profileHessian01.coeff n) =
      (n : K) * ((P.level : K) - (P.profileWeight : K) * (n : K)) *
        MvPolynomial.coeff (m.cons n)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) := by
    rw [P.coeff_profileHessian01]
    rw [show (n : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (n : K) by norm_num]
    rw [show (P.level : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (P.level : K) by norm_num]
    rw [show (P.profileWeight : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (P.profileWeight : K) by norm_num]
    simp only [← map_mul, ← map_sub]
    rw [MvPolynomial.coeff_C_mul, coeff_rayRawLongitudinalProfile]
  simp only [Finsupp.cons_zero]
  rw [hp]
  apply congrArg (fun f : Polynomial K => f.coeff _)
  rw [show (n : Polynomial K) = Polynomial.C (n : K) by norm_num]
  simp only [map_add, map_sub, map_mul, map_one]
  ring

/-- Whole-longitudinal recognition of the longitudinal Hessian row. -/
theorem QsOtherFacetRayProfileReesPackage.binaryProfileHessian11_longitudinal_coeff
    (P : QsOtherFacetRayProfileReesPackage C R) (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessian11Family).coeff n =
      MvPolynomial.C (Polynomial.X ^ (P.level - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (P.profileHessian11.coeff n) := by
  ext m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetRayProfileReesPackage.binaryProfileHessian11Family]
  rw [P.longitudinalEulerHessian_coeff]
  rw [P.coeff_binaryHomogenizedFamily]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  have hp : MvPolynomial.coeff m (P.profileHessian11.coeff n) =
      ((n : K) * ((n : K) - 1)) *
        MvPolynomial.coeff (m.cons n)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) := by
    rw [P.coeff_profileHessian11]
    rw [show (n : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (n : K) by norm_num]
    rw [show MvPolynomial.C (n : K) * (MvPolynomial.C (n : K) - 1) =
      MvPolynomial.C ((n : K) * ((n : K) - 1)) by
        rw [map_mul, map_sub, map_one]]
    rw [MvPolynomial.coeff_C_mul, coeff_rayRawLongitudinalProfile]
  simp only [Finsupp.cons_zero]
  rw [hp]
  apply congrArg (fun f : Polynomial K => f.coeff _)
  rw [show (n : Polynomial K) = Polynomial.C (n : K) by norm_num]
  simp only [map_add, map_sub, map_mul, map_one]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
