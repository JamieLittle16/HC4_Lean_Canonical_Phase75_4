import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryPivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryParameterEulerIdentity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryLongitudinalHessianCoefficients
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLongitudinalProfile
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetSuperfaceSchur
import Mathlib.Tactic

/-!
# A19.135--A19.136 / R18: active binary Schur pivot and exact Euler block

A19.134 proves nonvanishing of the relevant ordinary Hessian principal minor
of the binary-homogenized contact family.  A19.128 formulates the exact
closing clock using `permutedFamilyHessianFourBlock`, whose entries live after
the canonical parameter-first ring equivalence.

A19.135 closes that representation seam.  The active determinant of a
permuted family four-block is exactly the parameter-first image of the
corresponding ordinary Hessian principal minor.  Since the parameter-first map
is an equivalence, the three cyclic A19.134 pivots remain nonzero in the exact
Schur block consumed by A19.128.

A19.136 records the exact clock and convolution arithmetic needed by the
staircase residual adapter.  R18 additionally exposes the mixed
parameter/longitudinal and pure longitudinal Euler-Hessian coefficients before
specialising the parameter.  Together with A19.132's second parameter-Euler
identity, all three binary staircase factors therefore live in the same
polynomial coefficient ring as the cleared Schur series.

No localization or division by the pivot is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The active determinant of the state-free permuted family block is the
parameter-first image of the corresponding ordinary Hessian principal minor. -/
theorem permutedFamilyHessianFourBlock_activeDet_eq_parameterFirst_hessianPrincipalMinor
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedFamilyHessianFourBlock rho F).activeDet =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor F (rho 0) (rho 1)) := by
  unfold permutedFamilyHessianFourBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [map_sub, map_mul, map_mul]
  change
    parameterFirstHessian F (rho 0) (rho 0) *
          parameterFirstHessian F (rho 1) (rho 1) -
        parameterFirstHessian F (rho 0) (rho 1) *
          parameterFirstHessian F (rho 0) (rho 1) =
      parameterFirstHessian F (rho 0) (rho 0) *
          parameterFirstHessian F (rho 1) (rho 1) -
        parameterFirstHessian F (rho 0) (rho 1) *
          parameterFirstHessian F (rho 1) (rho 0)
  rw [parameterFirstHessian_symmetric F (rho 1) (rho 0)]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

-- CI anchor: elaborate the A19.136 convolution-order bridge on the refreshed inventory.

/-- A nonzero ordinary binary Hessian principal minor gives a nonzero active
determinant in the parameter-first permuted family block. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_permuted_activeDet_ne_zero_of_minor
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor P.binaryHomogenizedFamily
        (rho 0) (rho 1) ≠ 0) :
    (permutedFamilyHessianFourBlock rho P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_eq_parameterFirst_hessianPrincipalMinor]
  intro hzero
  apply hminor
  apply (parameterFirstEquiv K).injective
  simpa using hzero

/-- Every nonzero coefficient of the exact raw longitudinal profile lies in a
longitudinal degree whose binary weight is bounded by the top degree. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileWeight_mul_le_of_coeff_ne_zero
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {n : ℕ}
    (hn : Q.profile.coeff n ≠ 0) :
    n * P.profileWeight ≤ T.topFace.degree := by
  have hnle : n ≤ Q.profile.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hn
  calc
    n * P.profileWeight ≤ Q.profile.natDegree * P.profileWeight :=
      Nat.mul_le_mul_right P.profileWeight hnle
    _ ≤ T.topFace.degree := Q.support_bound

/-- Binary parameter orders of two actual longitudinal profile coefficients
add to the single residual order indexed by their longitudinal degree sum.
The support bounds remove all ambiguity from natural subtraction. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binary_profileOrder_add
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {i j : ℕ}
    (hi : Q.profile.coeff i ≠ 0)
    (hj : Q.profile.coeff j ≠ 0) :
    (T.topFace.degree - P.profileWeight * i) +
        (T.topFace.degree - P.profileWeight * j) =
      2 * T.topFace.degree - P.profileWeight * (i + j) := by
  have hiBound := Q.profileWeight_mul_le_of_coeff_ne_zero hi
  have hjBound := Q.profileWeight_mul_le_of_coeff_ne_zero hj
  rw [Nat.mul_comm i P.profileWeight] at hiBound
  rw [Nat.mul_comm j P.profileWeight] at hjBound
  rw [Nat.mul_add]
  omega

/-- Every quadratic binary-profile parameter order lies strictly before the
exact A19.128 Hessian clock.  The key input is the honest profile support
bound together with its degree-at-least-two witness. -/
theorem QsOtherFacetContactQuadraticReesPackage.binary_profileOrder_lt_hessianClock
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) :
    2 * T.topFace.degree - P.profileWeight * n <
      (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6 := by
  have htwoWeight :
      2 * P.profileWeight ≤ Q.profile.natDegree * P.profileWeight :=
    Nat.mul_le_mul_right P.profileWeight Q.degree_two_le
  have hbound : 2 * P.profileWeight ≤ T.topFace.degree :=
    le_trans htwoWeight Q.support_bound
  have hclock :
      2 * T.topFace.degree <
        (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6 := by
    rw [P.profileWeight_eq] at hbound
    omega
  exact lt_of_le_of_lt (Nat.sub_le _ _) hclock

/-- A19.128 therefore kills the cleared-Schur coefficient at every parameter
order that can carry a coefficient of the binary staircase Hessian residual. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSchurDetCore_coeff_profileOrder_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    ((permutedFamilyHessianFourBlock rho P.binaryHomogenizedFamily).schurDetCore).coeff
        (2 * T.topFace.degree - P.profileWeight * n) = 0 := by
  exact
    P.binaryHomogenized_permutedSchurDetCore_coeff_eq_zero_of_lt rho
      (P.binary_profileOrder_lt_hessianClock Q n)

/-- **R18 mixed Euler coefficient.**  Before any `tau = 1` specialization,
the mixed parameter/longitudinal Euler derivative has exactly the staircase
factor `n * (D-r*n)` on every source monomial. -/
theorem QsOtherFacetContactQuadraticReesPackage.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d
          (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily)) =
      (d (0 : Fin 4) : Polynomial K) *
        Polynomial.C
          ((T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [coeff_mvEuler]
  simp only [Polynomial.derivative_mul]
  have hconst :
      Polynomial.derivative (d (0 : Fin 4) : Polynomial K) = 0 := by
    simp
  rw [hconst, zero_mul, zero_add]
  calc
    Polynomial.X *
          ((d (0 : Fin 4) : Polynomial K) *
            Polynomial.derivative
              (MvPolynomial.coeff d P.binaryHomogenizedFamily)) =
        (d (0 : Fin 4) : Polynomial K) *
          (Polynomial.X * Polynomial.derivative
            (MvPolynomial.coeff d P.binaryHomogenizedFamily)) := by
      ring
    _ =
        (d (0 : Fin 4) : Polynomial K) *
          (Polynomial.C
              ((T.topFace.degree : K) -
                (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
            MvPolynomial.coeff d P.binaryHomogenizedFamily) := by
      rw [P.parameterEuler_coeff_binaryHomogenizedFamily d]
    _ =
        (d (0 : Fin 4) : Polynomial K) *
          Polynomial.C
            ((T.topFace.degree : K) -
              (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
          MvPolynomial.coeff d P.binaryHomogenizedFamily := by
      ring

/-- **R18 longitudinal Euler-Hessian coefficient.**  The pure longitudinal
Euler-scaled source Hessian has exactly the falling factor `n(n-1)` in the
same parameter polynomial ring. -/
theorem QsOtherFacetContactQuadraticReesPackage.longitudinalEulerHessian_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (HC4.Polynomial.eulerScaledHessian P.binaryHomogenizedFamily
          (0 : Fin 4) 0) =
      ((d (0 : Fin 4) : Polynomial K) *
          ((d (0 : Fin 4) : Polynomial K) - 1)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [coeff_eulerScaledHessian]
  simp only [if_pos]
  ring

/-- `.pr`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsPrSuperfaceSchurPermutation] using
    P.pr_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

/-- `.sp`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.sp_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsSpSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsSpSuperfaceSchurPermutation] using
    P.sp_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

/-- `.rq`: the exact binary Schur block has nonzero active determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.rq_binary_activeDet_ne_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsRqSuperfaceSchurPermutation P.binaryHomogenizedFamily).activeDet ≠ 0 := by
  apply P.binary_permuted_activeDet_ne_zero_of_minor
  simpa [qsRqSuperfaceSchurPermutation] using
    P.rq_binary_hessianPrincipalMinor_ne_zero R hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
