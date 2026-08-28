import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetResidualDegreeGap
import HC4.RationalRigidity.RankThreeDegreeOneAutonomousNormalForm
import Mathlib.Tactic

/-!
# A19.91: the lower degree-one `qs` ray cannot end in codimension two

A19.75/A19.79 identify the genuine lower `qs` ray with a primitive
coordinate-zero step and coefficient degree one.  A19.90 upgrades its
rank-three terminal equation to the exact autonomous normal form

    T = X - X^2.

This is stronger than the endpoint-pencil determinant when the far endpoint
has two transverse zero coordinates.  Substituting two far-end zero equations
into the raw target identity makes the remaining coefficient factor as

    A * B * (C + S)^2 * (A + B - 1)

(or one of its two cyclic companions).  The starting `qs` endpoint has
positive transverse coordinates, so every factor except the square is
nonzero.  Hence the third far transverse coordinate vanishes as well.

The far endpoint is therefore literally `(1,0,0,0)`, of ordinary degree one.
But A19.89 produces an actual strict-low source monomial of ordinary degree at
least three and strictly below that far endpoint.  This contradiction removes
the codimension-two far-end alternative without a balance relation and without
introducing another descent measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.RationalRigidity
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem degreeOne_raw_first_two_zero_forces_third
    {A B C : ℕ} {Q R S : K}
    (hA : 0 < A) (hB : 0 < B)
    (hraw :
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S)
    (hQ0 : (A : K) + Q = 0)
    (hR0 : (B : K) + R = 0) :
    (C : K) + S = 0 := by
  have hQ : Q = -(A : K) := by linear_combination hQ0
  have hR : R = -(B : K) := by linear_combination hR0
  have h2 := congrArg (Polynomial.eval (2 : K)) hraw
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_pow] at h2
  rw [HC4.Polynomial.eval_rankThreeEtaDenominatorPolynomial,
    HC4.Polynomial.eval_rankThreeEtaNumeratorPolynomial] at h2
  rw [hQ, hR] at h2
  unfold HC4.Polynomial.rankThreeEtaNumerator
    HC4.Polynomial.rankThreeEtaDenominator
    HC4.Polynomial.rankThreeLogProduct
    HC4.Polynomial.rankThreeLogSum
    HC4.Polynomial.rankThreeWeightedCofactorSum
    HC4.Polynomial.rankThreeDirectionDefect at h2
  have hfactor4 :
      (4 : K) * (A : K) * (B : K) * ((C : K) + S) ^ 2 *
        ((A : K) + (B : K) - 1) = 0 := by
    linear_combination h2
  have h4 : (4 : K) ≠ 0 := by norm_num
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hABm1 : (A : K) + (B : K) - 1 ≠ 0 := by
    intro hz
    have habK : (A : K) + (B : K) = 1 := by linear_combination hz
    have habN : A + B = 1 := by exact_mod_cast habK
    omega
  have hsquare : ((C : K) + S) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfactor4 with hleft | hlast
    · rcases mul_eq_zero.mp hleft with hleft | hsquare
      · rcases mul_eq_zero.mp hleft with hleft | hBz
        · rcases mul_eq_zero.mp hleft with h4z | hAz
          · exact (h4 h4z).elim
          · exact (hA0 hAz).elim
        · exact (hB0 hBz).elim
      · exact hsquare
    · exact (hABm1 hlast).elim
  rw [pow_two] at hsquare
  exact (mul_self_eq_zero.mp hsquare)

private theorem degreeOne_raw_first_third_zero_forces_second
    {A B C : ℕ} {Q R S : K}
    (hA : 0 < A) (hC : 0 < C)
    (hraw :
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S)
    (hQ0 : (A : K) + Q = 0)
    (hS0 : (C : K) + S = 0) :
    (B : K) + R = 0 := by
  have hQ : Q = -(A : K) := by linear_combination hQ0
  have hS : S = -(C : K) := by linear_combination hS0
  have h2 := congrArg (Polynomial.eval (2 : K)) hraw
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_pow] at h2
  rw [HC4.Polynomial.eval_rankThreeEtaDenominatorPolynomial,
    HC4.Polynomial.eval_rankThreeEtaNumeratorPolynomial] at h2
  rw [hQ, hS] at h2
  unfold HC4.Polynomial.rankThreeEtaNumerator
    HC4.Polynomial.rankThreeEtaDenominator
    HC4.Polynomial.rankThreeLogProduct
    HC4.Polynomial.rankThreeLogSum
    HC4.Polynomial.rankThreeWeightedCofactorSum
    HC4.Polynomial.rankThreeDirectionDefect at h2
  have hfactor4 :
      (4 : K) * (A : K) * (C : K) * ((B : K) + R) ^ 2 *
        ((A : K) + (C : K) - 1) = 0 := by
    linear_combination h2
  have h4 : (4 : K) ≠ 0 := by norm_num
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hACm1 : (A : K) + (C : K) - 1 ≠ 0 := by
    intro hz
    have hacK : (A : K) + (C : K) = 1 := by linear_combination hz
    have hacN : A + C = 1 := by exact_mod_cast hacK
    omega
  have hsquare : ((B : K) + R) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfactor4 with hleft | hlast
    · rcases mul_eq_zero.mp hleft with hleft | hsquare
      · rcases mul_eq_zero.mp hleft with hleft | hCz
        · rcases mul_eq_zero.mp hleft with h4z | hAz
          · exact (h4 h4z).elim
          · exact (hA0 hAz).elim
        · exact (hC0 hCz).elim
      · exact hsquare
    · exact (hACm1 hlast).elim
  rw [pow_two] at hsquare
  exact (mul_self_eq_zero.mp hsquare)

private theorem degreeOne_raw_last_two_zero_forces_first
    {A B C : ℕ} {Q R S : K}
    (hB : 0 < B) (hC : 0 < C)
    (hraw :
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S)
    (hR0 : (B : K) + R = 0)
    (hS0 : (C : K) + S = 0) :
    (A : K) + Q = 0 := by
  have hR : R = -(B : K) := by linear_combination hR0
  have hS : S = -(C : K) := by linear_combination hS0
  have h2 := congrArg (Polynomial.eval (2 : K)) hraw
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_pow] at h2
  rw [HC4.Polynomial.eval_rankThreeEtaDenominatorPolynomial,
    HC4.Polynomial.eval_rankThreeEtaNumeratorPolynomial] at h2
  rw [hR, hS] at h2
  unfold HC4.Polynomial.rankThreeEtaNumerator
    HC4.Polynomial.rankThreeEtaDenominator
    HC4.Polynomial.rankThreeLogProduct
    HC4.Polynomial.rankThreeLogSum
    HC4.Polynomial.rankThreeWeightedCofactorSum
    HC4.Polynomial.rankThreeDirectionDefect at h2
  have hfactor4 :
      (4 : K) * (B : K) * (C : K) * ((A : K) + Q) ^ 2 *
        ((B : K) + (C : K) - 1) = 0 := by
    linear_combination h2
  have h4 : (4 : K) ≠ 0 := by norm_num
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hBCm1 : (B : K) + (C : K) - 1 ≠ 0 := by
    intro hz
    have hbcK : (B : K) + (C : K) = 1 := by linear_combination hz
    have hbcN : B + C = 1 := by exact_mod_cast hbcK
    omega
  have hsquare : ((A : K) + Q) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfactor4 with hleft | hlast
    · rcases mul_eq_zero.mp hleft with hleft | hsquare
      · rcases mul_eq_zero.mp hleft with hleft | hCz
        · rcases mul_eq_zero.mp hleft with h4z | hBz
          · exact (h4 h4z).elim
          · exact (hB0 hBz).elim
        · exact (hC0 hCz).elim
      · exact hsquare
    · exact (hBCm1 hlast).elim
  rw [pow_two] at hsquare
  exact (mul_self_eq_zero.mp hsquare)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **A19.91 lower codimension-two elimination.**  Under the surviving
rank-three `.qs` hypothesis, the actual degree-one outside endpoint cannot be
codimension two. -/
theorem qs_ray_outside_codimensionTwo_impossible
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtTwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary
      C.ray.outsideExponent) : False := by
  have hcoords := HC4.Newton.mvRankThreeOnFacet_qs hthree
  have hA : 0 < C.ray.facetExponent 1 := hcoords.2.1
  have hB : 0 < C.ray.facetExponent 2 := hcoords.2.2.1
  have hC : 0 < C.ray.facetExponent 3 := hcoords.2.2.2
  have hphiDeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hphi0 : C.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    C.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hcert0 := C.ray.zero_rankThree_terminalCertificate C.hessian_zero hthree
  have hcert :
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := C.ray.zeroCoefficientPolynomial)
        ((C.ray.facetExponent 1 : ℕ) : K)
        ((C.ray.facetExponent 2 : ℕ) : K)
        ((C.ray.facetExponent 3 : ℕ) : K)
        (1 : K)
        (C.ray.zeroSlope (1 : Fin 4))
        (C.ray.zeroSlope (2 : Fin 4))
        (C.ray.zeroSlope (3 : Fin 4)) := by
    simpa only [Nat.cast_one] using hcert0
  rcases
      HC4.RationalRigidity.exists_rankThree_raw_target_X_sub_X_sq_identity_of_source_degree_one
        hA hB hC (by norm_num) hphiDeg hphi0 hcert with
    ⟨_hPone, _hphi1, hraw⟩

  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have haff := C.ray.zero_support_affine C.ray.outside_mem_face
  have h1aff :
      ((C.ray.outsideExponent (1 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (1 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (1 : Fin 4) := by
    have h := congrFun haff (1 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  have h2aff :
      ((C.ray.outsideExponent (2 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (2 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (2 : Fin 4) := by
    have h := congrFun haff (2 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h
  have h3aff :
      ((C.ray.outsideExponent (3 : Fin 4) : ℕ) : K) =
        ((C.ray.facetExponent (3 : Fin 4) : ℕ) : K) +
          C.ray.zeroSlope (3 : Fin 4) := by
    have h := congrFun haff (3 : Fin 4)
    simpa [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection, hout0] using h

  have hpairs :
      (C.ray.outsideExponent (1 : Fin 4) = 0 ∧
        C.ray.outsideExponent (2 : Fin 4) = 0) ∨
      (C.ray.outsideExponent (1 : Fin 4) = 0 ∧
        C.ray.outsideExponent (3 : Fin 4) = 0) ∨
      (C.ray.outsideExponent (2 : Fin 4) = 0 ∧
        C.ray.outsideExponent (3 : Fin 4) = 0) := by
    rcases houtTwo with ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp [hout0] at hij hi hj ⊢
  have hall :
      C.ray.outsideExponent (1 : Fin 4) = 0 ∧
      C.ray.outsideExponent (2 : Fin 4) = 0 ∧
      C.ray.outsideExponent (3 : Fin 4) = 0 := by
    rcases hpairs with h12 | h13 | h23
    · have hQ0 :
          ((C.ray.facetExponent 1 : ℕ) : K) + C.ray.zeroSlope 1 = 0 := by
        rw [h12.1] at h1aff
        simpa using h1aff.symm
      have hR0 :
          ((C.ray.facetExponent 2 : ℕ) : K) + C.ray.zeroSlope 2 = 0 := by
        rw [h12.2] at h2aff
        simpa using h2aff.symm
      have hS0 := degreeOne_raw_first_two_zero_forces_third
        hA hB hraw hQ0 hR0
      have h3K : ((C.ray.outsideExponent 3 : ℕ) : K) = 0 :=
        h3aff.trans hS0
      have h3 : C.ray.outsideExponent 3 = 0 := by exact_mod_cast h3K
      exact ⟨h12.1, h12.2, h3⟩
    · have hQ0 :
          ((C.ray.facetExponent 1 : ℕ) : K) + C.ray.zeroSlope 1 = 0 := by
        rw [h13.1] at h1aff
        simpa using h1aff.symm
      have hS0 :
          ((C.ray.facetExponent 3 : ℕ) : K) + C.ray.zeroSlope 3 = 0 := by
        rw [h13.2] at h3aff
        simpa using h3aff.symm
      have hR0 := degreeOne_raw_first_third_zero_forces_second
        hA hC hraw hQ0 hS0
      have h2K : ((C.ray.outsideExponent 2 : ℕ) : K) = 0 :=
        h2aff.trans hR0
      have h2 : C.ray.outsideExponent 2 = 0 := by exact_mod_cast h2K
      exact ⟨h13.1, h2, h13.2⟩
    · have hR0 :
          ((C.ray.facetExponent 2 : ℕ) : K) + C.ray.zeroSlope 2 = 0 := by
        rw [h23.1] at h2aff
        simpa using h2aff.symm
      have hS0 :
          ((C.ray.facetExponent 3 : ℕ) : K) + C.ray.zeroSlope 3 = 0 := by
        rw [h23.2] at h3aff
        simpa using h3aff.symm
      have hQ0 := degreeOne_raw_last_two_zero_forces_first
        hB hC hraw hR0 hS0
      have h1K : ((C.ray.outsideExponent 1 : ℕ) : K) = 0 :=
        h1aff.trans hQ0
      have h1 : C.ray.outsideExponent 1 = 0 := by exact_mod_cast h1K
      exact ⟨h1, h23.1, h23.2⟩

  have houtDeg : HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent = 1 := by
    simp [HC4.Polynomial.ordinaryDegree4, hout0, hall.1, hall.2.1, hall.2.2]
  rcases C.qs_ray_strictLow_sourceCodimensionTwo_degree_lt_outside hthree with
    ⟨d, _hd, hdeg3, _hd0, _htwo, hlt⟩
  rw [houtDeg] at hlt
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
