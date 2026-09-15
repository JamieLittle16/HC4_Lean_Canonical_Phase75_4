import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayBinaryHomogenization
import Mathlib.Tactic

/-!
# A19.R18.20: ray-native binary profile determinant

A19.R18.19 replaces the old contact-first binary filtration by the doubled
ray-leading Rees.  Its transverse inflation leaves the exact binary parameter
order

    level - profileWeight * d₀

on every represented source monomial, and already recognises the three
parameter/longitudinal Hessian rows coefficientwise.

This module performs the remaining representation bookkeeping once:

* transverse inflation sends the pure ray Hessian clock to the exact binary
  clock `4 * level - 2 * profileWeight`;
* the determinant of the three recognised profile-Hessian rows has exact
  longitudinal coefficient order `2 * level - profileWeight * n`;
* vanishing of those exact family layers is therefore equivalent to vanishing
  of the integral profile determinant coefficients.

No Schur-product implication is asserted here.  In particular, the mixed
active/profile correction exposed by the previous contact calculation remains
an explicit downstream obligation; R18.20 only removes the representation and
clock bookkeeping from that obligation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Inflating one source coordinate by `tau^slope` raises a pure Hessian defect
by exactly `2 * slope`.  This is the arbitrary-slope form of the old unit
inflation bookkeeping. -/
theorem kernelInflateHom_hasHessianDefect_add_two_mul
    (kernel : Fin 4)
    (slope Delta : ℕ)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) F Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (kernelInflateHom (K := K) kernel slope F)
      (Delta + 2 * slope) := by
  unfold HasPolynomialFamilyHessianDefect at hdef ⊢
  rw [hessianDeterminant_kernelInflateHom, hdef, kernelInflateHom_C]
  have hpow :
      ((Polynomial.X : Polynomial K) ^ slope) ^ 2 *
          Polynomial.X ^ Delta =
        Polynomial.X ^ (Delta + 2 * slope) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hC := congrArg
    (fun p : Polynomial K =>
      (MvPolynomial.C p : MvPolynomial (Fin 4) (Polynomial K))) hpow
  simpa only [map_mul, map_pow] using hC

/-- Three weighted transverse inflations add exactly twice the sum of their
three source weights to the Hessian defect. -/
theorem weightedTransverseInflateFamily_hasHessianDefect
    (W : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) F Delta) :
    HasPolynomialFamilyHessianDefect (K := K)
      (weightedTransverseInflateFamily (K := K) W F)
      (Delta + 2 * W 1 + 2 * W 2 + 2 * W 3) := by
  have h1 := kernelInflateHom_hasHessianDefect_add_two_mul
    (K := K) (1 : Fin 4) (W 1) Delta F hdef
  have h2 := kernelInflateHom_hasHessianDefect_add_two_mul
    (K := K) (2 : Fin 4) (W 2) (Delta + 2 * W 1)
      (kernelInflateHom (K := K) (1 : Fin 4) (W 1) F) h1
  have h3 := kernelInflateHom_hasHessianDefect_add_two_mul
    (K := K) (3 : Fin 4) (W 3) (Delta + 2 * W 1 + 2 * W 2)
      (kernelInflateHom (K := K) (2 : Fin 4) (W 2)
        (kernelInflateHom (K := K) (1 : Fin 4) (W 1) F)) h2
  simpa [weightedTransverseInflateFamily, Nat.add_assoc] using h3

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {R : QsOtherFacetRayReverseReesPackage C}

/-- **Exact normalized Hessian clock.**  The doubled ray Rees starts with
clock `4*level - 2*sum weight`; reinflating the three transverse source
coordinates adds back exactly their six row/column weight contributions and
leaves only the longitudinal binary weight. -/
theorem QsOtherFacetRayProfileReesPackage.binaryHomogenized_hessianDefect
    (P : QsOtherFacetRayProfileReesPackage C R) :
    HasPolynomialFamilyHessianDefect (K := K)
      P.binaryHomogenizedFamily P.binaryHessianClock := by
  have hray : HasPolynomialFamilyHessianDefect (K := K)
      P.rayFamily (4 * P.level - 2 * ∑ i : Fin 4, P.weight i) := by
    simpa [QsOtherFacetRayProfileReesPackage.rayFamily] using P.hessianDefect
  have h := weightedTransverseInflateFamily_hasHessianDefect
    (K := K) P.weight P.rayFamily
      (4 * P.level - 2 * ∑ i : Fin 4, P.weight i) hray
  have hsum :
      ∑ i : Fin 4, P.weight i =
        P.weight 0 + P.weight 1 + P.weight 2 + P.weight 3 := by
    rw [Fin.sum_univ_four]
  have hmargin := P.two_level_lt_defect
  rw [hsum] at hmargin
  have hclock :
      (4 * P.level -
          2 * (P.weight 0 + P.weight 1 + P.weight 2 + P.weight 3)) +
          2 * P.weight 1 + 2 * P.weight 2 + 2 * P.weight 3 =
        4 * P.level - 2 * P.profileWeight := by
    rw [P.profileWeight_eq]
    omega
  rw [hsum] at h
  rw [hclock] at h
  simpa [QsOtherFacetRayProfileReesPackage.binaryHomogenizedFamily,
    QsOtherFacetRayProfileReesPackage.binaryHessianClock] using h

/-- Every parameter layer before the normalized binary Hessian clock has zero
full source Hessian determinant. -/
theorem QsOtherFacetRayProfileReesPackage.binaryHomogenized_determinantLayer_eq_zero_of_lt
    (P : QsOtherFacetRayProfileReesPackage C R)
    {q : ℕ}
    (hq : q < P.binaryHessianClock) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant P.binaryHomogenizedFamily) q = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    P.binaryHomogenizedFamily P.binaryHomogenized_hessianDefect hq

/-- In particular every quadratic profile order is preclosing for the exact
binary source determinant. -/
theorem QsOtherFacetRayProfileReesPackage.binaryHomogenized_determinantLayer_profileOrder_eq_zero
    (P : QsOtherFacetRayProfileReesPackage C R)
    (n : ℕ) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant P.binaryHomogenizedFamily)
      (2 * P.level - P.profileWeight * n) = 0 := by
  exact P.binaryHomogenized_determinantLayer_eq_zero_of_lt
    (P.quadraticProfileOrder_lt_clock n)

/-- A nonzero coefficient of the unchanged longitudinal source profile occurs
at a degree admitted by the ray binary weight bound. -/
theorem QsOtherFacetRayProfileReesPackage.profileWeight_mul_le_of_rawProfile_coeff_ne_zero
    (P : QsOtherFacetRayProfileReesPackage C R)
    {n : ℕ}
    (hn : (rayRawLongitudinalProfile (T := T)).coeff n ≠ 0) :
    P.profileWeight * n ≤ P.level := by
  by_contra hnot
  apply hn
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  rw [rayRawLongitudinalProfile]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  by_contra hcoeff
  have hmem :
      m.cons n ∈
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hbound := P.profileWeight_mul_longitudinal_le hmem
  have hzero : (m.cons n) (0 : Fin 4) = n := by simp
  rw [hzero] at hbound
  omega

/-- Binary parameter orders of two actual longitudinal source coefficients add
to the unique quadratic profile order indexed by their longitudinal degree
sum. -/
theorem QsOtherFacetRayProfileReesPackage.binary_profileOrder_add
    (P : QsOtherFacetRayProfileReesPackage C R)
    {i j : ℕ}
    (hi : (rayRawLongitudinalProfile (T := T)).coeff i ≠ 0)
    (hj : (rayRawLongitudinalProfile (T := T)).coeff j ≠ 0) :
    (P.level - P.profileWeight * i) +
        (P.level - P.profileWeight * j) =
      2 * P.level - P.profileWeight * (i + j) := by
  have hiBound := P.profileWeight_mul_le_of_rawProfile_coeff_ne_zero hi
  have hjBound := P.profileWeight_mul_le_of_rawProfile_coeff_ne_zero hj
  rw [Nat.mul_add]
  omega

/-- **Whole ray-native profile determinant extraction.**  Longitudinal degree
`n` of the binary parameter/longitudinal Hessian determinant is exactly the
single parameter monomial `tau^(2*level-profileWeight*n)` times the integral
profile determinant coefficient. -/
theorem QsOtherFacetRayProfileReesPackage.binaryProfileHessianDetFamily_longitudinal_coeff
    (P : QsOtherFacetRayProfileReesPackage C R)
    (n : ℕ) :
    (MvPolynomial.finSuccEquiv (Polynomial K) 3
      P.binaryProfileHessianDetFamily).coeff n =
      MvPolynomial.C
          ((Polynomial.X : Polynomial K) ^
            (2 * P.level - P.profileWeight * n)) *
        MvPolynomial.map Polynomial.C (P.profileHessianDet.coeff n) := by
  have h0011 :
      (((MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian00Family) *
        (MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian11Family)).coeff n) =
        MvPolynomial.C
            ((Polynomial.X : Polynomial K) ^
              (2 * P.level - P.profileWeight * n)) *
          MvPolynomial.map Polynomial.C
            ((P.profileHessian00 * P.profileHessian11).coeff n) := by
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [P.binaryProfileHessian00_longitudinal_coeff ij.1,
      P.binaryProfileHessian11_longitudinal_coeff ij.2]
    simp only [map_mul]
    by_cases hi : (rayRawLongitudinalProfile (T := T)).coeff ij.1 = 0
    · have h00 : P.profileHessian00.coeff ij.1 = 0 := by
        rw [P.coeff_profileHessian00, hi]
        simp
      simp [h00]
    · by_cases hj : (rayRawLongitudinalProfile (T := T)).coeff ij.2 = 0
      · have h11 : P.profileHessian11.coeff ij.2 = 0 := by
          rw [P.coeff_profileHessian11, hj]
          simp
        simp [h11]
      · have horder := P.binary_profileOrder_add hi hj
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [hsum] at horder
        have hC :
            MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.1)) *
              MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.2)) =
            (MvPolynomial.C
              ((Polynomial.X : Polynomial K) ^
                (2 * P.level - P.profileWeight * n)) :
              MvPolynomial (Fin 3) (Polynomial K)) := by
          rw [← MvPolynomial.C_mul, ← pow_add, horder]
        calc
          (MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.1)) *
              MvPolynomial.map Polynomial.C
                (P.profileHessian00.coeff ij.1)) *
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.2)) *
                MvPolynomial.map Polynomial.C
                  (P.profileHessian11.coeff ij.2)) =
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.1)) *
                MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.2))) *
                (MvPolynomial.map Polynomial.C
                    (P.profileHessian00.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (P.profileHessian11.coeff ij.2)) := by ring
          _ = MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (2 * P.level - P.profileWeight * n)) *
                (MvPolynomial.map Polynomial.C
                    (P.profileHessian00.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (P.profileHessian11.coeff ij.2)) := by rw [hC]

  have h0101 :
      (((MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian01Family) *
        (MvPolynomial.finSuccEquiv (Polynomial K) 3
          P.binaryProfileHessian01Family)).coeff n) =
        MvPolynomial.C
            ((Polynomial.X : Polynomial K) ^
              (2 * P.level - P.profileWeight * n)) *
          MvPolynomial.map Polynomial.C
            ((P.profileHessian01 * P.profileHessian01).coeff n) := by
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [P.binaryProfileHessian01_longitudinal_coeff ij.1,
      P.binaryProfileHessian01_longitudinal_coeff ij.2]
    simp only [map_mul]
    by_cases hi : (rayRawLongitudinalProfile (T := T)).coeff ij.1 = 0
    · have h01 : P.profileHessian01.coeff ij.1 = 0 := by
        rw [P.coeff_profileHessian01, hi]
        simp
      simp [h01]
    · by_cases hj : (rayRawLongitudinalProfile (T := T)).coeff ij.2 = 0
      · have h01 : P.profileHessian01.coeff ij.2 = 0 := by
          rw [P.coeff_profileHessian01, hj]
          simp
        simp [h01]
      · have horder := P.binary_profileOrder_add hi hj
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        rw [hsum] at horder
        have hC :
            MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.1)) *
              MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.2)) =
            (MvPolynomial.C
              ((Polynomial.X : Polynomial K) ^
                (2 * P.level - P.profileWeight * n)) :
              MvPolynomial (Fin 3) (Polynomial K)) := by
          rw [← MvPolynomial.C_mul, ← pow_add, horder]
        calc
          (MvPolynomial.C
                ((Polynomial.X : Polynomial K) ^
                  (P.level - P.profileWeight * ij.1)) *
              MvPolynomial.map Polynomial.C
                (P.profileHessian01.coeff ij.1)) *
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.2)) *
                MvPolynomial.map Polynomial.C
                  (P.profileHessian01.coeff ij.2)) =
              (MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.1)) *
                MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (P.level - P.profileWeight * ij.2))) *
                (MvPolynomial.map Polynomial.C
                    (P.profileHessian01.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (P.profileHessian01.coeff ij.2)) := by ring
          _ = MvPolynomial.C
                  ((Polynomial.X : Polynomial K) ^
                    (2 * P.level - P.profileWeight * n)) *
                (MvPolynomial.map Polynomial.C
                    (P.profileHessian01.coeff ij.1) *
                  MvPolynomial.map Polynomial.C
                    (P.profileHessian01.coeff ij.2)) := by rw [hC]

  rw [QsOtherFacetRayProfileReesPackage.binaryProfileHessianDetFamily]
  simp only [map_sub, map_mul, Polynomial.coeff_sub]
  rw [h0011, h0101]
  rw [QsOtherFacetRayProfileReesPackage.profileHessianDet,
    Polynomial.coeff_sub, map_sub]
  ring

/-- A zero binary family determinant layer at the exact quadratic profile order
forces the corresponding integral ray-profile determinant coefficient to
vanish. -/
theorem QsOtherFacetRayProfileReesPackage.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer
    (P : QsOtherFacetRayProfileReesPackage C R)
    (n : ℕ)
    (hzero :
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * P.level - P.profileWeight * n) = 0) :
    P.profileHessianDet.coeff n = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  have hlong := P.binaryProfileHessianDetFamily_longitudinal_coeff n
  have hm := congrArg
    (fun A : MvPolynomial (Fin 3) (Polynomial K) => MvPolynomial.coeff m A)
    hlong
  have hmN := congrArg
    (fun q : Polynomial K =>
      q.coeff (2 * P.level - P.profileWeight * n)) hm
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hmN
  rw [← familyParameterLayer_coeff] at hmN
  rw [hzero] at hmN
  simp only [MvPolynomial.coeff_zero] at hmN
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hmN
  have hrhs :
      (((Polynomial.X : Polynomial K) ^
          (2 * P.level - P.profileWeight * n) *
        Polynomial.C (MvPolynomial.coeff m (P.profileHessianDet.coeff n))).coeff
          (2 * P.level - P.profileWeight * n)) =
        MvPolynomial.coeff m (P.profileHessianDet.coeff n) := by
    simpa using
      (Polynomial.coeff_X_pow_mul
        (Polynomial.C (MvPolynomial.coeff m (P.profileHessianDet.coeff n)))
        (2 * P.level - P.profileWeight * n) 0)
  rw [hrhs] at hmN
  exact hmN.symm

/-- If every exact quadratic layer of the ray-native binary profile determinant
vanishes, then the whole integral profile determinant is zero. -/
theorem QsOtherFacetRayProfileReesPackage.profileHessianDet_eq_zero_of_binaryFamily_layers
    (P : QsOtherFacetRayProfileReesPackage C R)
    (hlayers : ∀ n : ℕ,
      familyParameterLayer P.binaryProfileHessianDetFamily
        (2 * P.level - P.profileWeight * n) = 0) :
    P.profileHessianDet = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero]
  exact P.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer n (hlayers n)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
