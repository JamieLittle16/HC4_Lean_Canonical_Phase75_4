import HC4.RationalRigidity.RankThreeDegreeOneAutonomousNormalForm
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

-- Keep this algebra layer independent of valuation restart-state records.

/-!
# A19.91 codimension-two degree-one algebra

This module contains the small algebraic core used by the lower `qs` ray
codimension-two elimination.  It deliberately has no dependency on the large
restart-state records: the geometric file extracts plain exponents and slopes,
then hands them to these lemmas.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- If the first two transverse endpoint coordinates vanish, the autonomous
rank-three degree-one identity forces the third to vanish as well. -/
theorem degreeOneRaw_firstTwoZero_forcesThird
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
    linear_combination -h2
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
  exact mul_self_eq_zero.mp hsquare

/-- Cyclic companion of `degreeOneRaw_firstTwoZero_forcesThird`. -/
theorem degreeOneRaw_firstThirdZero_forcesSecond
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
    linear_combination -h2
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
  exact mul_self_eq_zero.mp hsquare

/-- Cyclic companion of `degreeOneRaw_firstTwoZero_forcesThird`. -/
theorem degreeOneRaw_lastTwoZero_forcesFirst
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
    linear_combination -h2
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
  exact mul_self_eq_zero.mp hsquare

/-- Pure finite-coordinate extraction: if coordinate zero is one and the
exponent lies on a codimension-two boundary, two of the three transverse
coordinates vanish. -/
theorem transversePair_zero_of_codimensionTwoBoundary
    (a : Fin 4 →₀ ℕ)
    (h0 : a (0 : Fin 4) = 1)
    (htwo : HC4.Newton.MvExponentOnCodimensionTwoBoundary a) :
    (a (1 : Fin 4) = 0 ∧ a (2 : Fin 4) = 0) ∨
      (a (1 : Fin 4) = 0 ∧ a (3 : Fin 4) = 0) ∨
      (a (2 : Fin 4) = 0 ∧ a (3 : Fin 4) = 0) := by
  rcases htwo with ⟨i, j, hij, hi, hj⟩
  fin_cases i <;> fin_cases j <;> simp_all

/-- Once geometry has been reduced to three affine endpoint equations, the
pure algebra above upgrades any vanishing transverse pair to vanishing of all
three transverse coordinates. -/
theorem degreeOneRaw_codimensionTwoPair_forcesAll
    {A B C x1 x2 x3 : ℕ} {Q R S : K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hraw :
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S)
    (h1aff : (x1 : K) = (A : K) + Q)
    (h2aff : (x2 : K) = (B : K) + R)
    (h3aff : (x3 : K) = (C : K) + S)
    (hpairs :
      (x1 = 0 ∧ x2 = 0) ∨
        (x1 = 0 ∧ x3 = 0) ∨
        (x2 = 0 ∧ x3 = 0)) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  rcases hpairs with h12 | h13 | h23
  · have hQ0 : (A : K) + Q = 0 := by
      rw [h12.1] at h1aff
      simpa using h1aff.symm
    have hR0 : (B : K) + R = 0 := by
      rw [h12.2] at h2aff
      simpa using h2aff.symm
    have hS0 := degreeOneRaw_firstTwoZero_forcesThird hA hB hraw hQ0 hR0
    have h3K : (x3 : K) = 0 := h3aff.trans hS0
    have hx3 : x3 = 0 := by exact_mod_cast h3K
    exact ⟨h12.1, h12.2, hx3⟩
  · have hQ0 : (A : K) + Q = 0 := by
      rw [h13.1] at h1aff
      simpa using h1aff.symm
    have hS0 : (C : K) + S = 0 := by
      rw [h13.2] at h3aff
      simpa using h3aff.symm
    have hR0 := degreeOneRaw_firstThirdZero_forcesSecond hA hC hraw hQ0 hS0
    have h2K : (x2 : K) = 0 := h2aff.trans hR0
    have hx2 : x2 = 0 := by exact_mod_cast h2K
    exact ⟨h13.1, hx2, h13.2⟩
  · have hR0 : (B : K) + R = 0 := by
      rw [h23.1] at h2aff
      simpa using h2aff.symm
    have hS0 : (C : K) + S = 0 := by
      rw [h23.2] at h3aff
      simpa using h3aff.symm
    have hQ0 := degreeOneRaw_lastTwoZero_forcesFirst hB hC hraw hR0 hS0
    have h1K : (x1 : K) = 0 := h1aff.trans hQ0
    have hx1 : x1 = 0 := by exact_mod_cast h1K
    exact ⟨hx1, h23.1, h23.2⟩

/-- State-free A19.90 extraction specialized to the unit longitudinal step.
The expensive construction now lives upstream in the dedicated A19.90 theorem;
this adapter is only a pinned application with the exact interface A19.91 uses. -/
theorem degreeOneTerminal_rawIdentity
    [IsAlgClosed K]
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S) :
    (Polynomial.X - Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S =
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
        (A : K) (B : K) (C : K) (1 : K) Q R S := by
  exact
    HC4.RationalRigidity.rankThree_raw_target_X_sub_X_sq_identity_of_source_degree_one_unit_step
      (K := K) (A := A) (B := B) (C := C)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC hphiDeg hphi0 hcert

/-- State-free A19.91 adapter: once the autonomous raw identity has been
extracted, the codimension-two endpoint conclusion is a cheap composition of
precompiled algebra lemmas. -/
theorem degreeOneTerminal_codimensionTwoPair_forcesAll
    [IsAlgClosed K]
    {A B C x1 x2 x3 : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S)
    (h1aff : (x1 : K) = (A : K) + Q)
    (h2aff : (x2 : K) = (B : K) + R)
    (h3aff : (x3 : K) = (C : K) + S)
    (hpairs :
      (x1 = 0 ∧ x2 = 0) ∨
        (x1 = 0 ∧ x3 = 0) ∨
        (x2 = 0 ∧ x3 = 0)) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have hraw := degreeOneTerminal_rawIdentity
    hA hB hC hphiDeg hphi0 hcert
  exact degreeOneRaw_codimensionTwoPair_forcesAll
    hA hB hC hraw h1aff h2aff h3aff hpairs

end

end HC4.Valuation