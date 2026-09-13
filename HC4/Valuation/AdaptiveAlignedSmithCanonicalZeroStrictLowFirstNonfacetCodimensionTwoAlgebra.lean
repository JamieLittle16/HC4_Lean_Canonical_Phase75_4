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

The final endpoint arithmetic only uses the autonomous raw relation at
`rho = 2`.  Accordingly the public algebra seam below is scalar: no downstream
theorem needs to carry or normalise the full polynomial identity.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- If the first two transverse endpoint coordinates vanish, the raw relation
at `rho = 2` forces the third to vanish as well. -/
theorem degreeOneRaw_firstTwoZero_forcesThird
    {A B C : ℕ} {Q R S : K}
    (hA : 0 < A) (hB : 0 < B)
    (h2 :
      (-2 : K) *
          Polynomial.eval (2 : K)
            (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
              (A : K) (B : K) (C : K) (1 : K) Q R S) =
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S))
    (hQ0 : (A : K) + Q = 0)
    (hR0 : (B : K) + R = 0) :
    (C : K) + S = 0 := by
  have hQ : Q = -(A : K) := by linear_combination hQ0
  have hR : R = -(B : K) := by linear_combination hR0
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
    (h2 :
      (-2 : K) *
          Polynomial.eval (2 : K)
            (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
              (A : K) (B : K) (C : K) (1 : K) Q R S) =
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S))
    (hQ0 : (A : K) + Q = 0)
    (hS0 : (C : K) + S = 0) :
    (B : K) + R = 0 := by
  have hQ : Q = -(A : K) := by linear_combination hQ0
  have hS : S = -(C : K) := by linear_combination hS0
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
    (h2 :
      (-2 : K) *
          Polynomial.eval (2 : K)
            (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
              (A : K) (B : K) (C : K) (1 : K) Q R S) =
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S))
    (hR0 : (B : K) + R = 0)
    (hS0 : (C : K) + S = 0) :
    (A : K) + Q = 0 := by
  have hR : R = -(B : K) := by linear_combination hR0
  have hS : S = -(C : K) := by linear_combination hS0
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
raw relation at `rho = 2` upgrades any vanishing transverse pair to vanishing
of all three transverse coordinates. -/
theorem degreeOneRaw_codimensionTwoPair_forcesAll
    {A B C x1 x2 x3 : ℕ} {Q R S : K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h2 :
      (-2 : K) *
          Polynomial.eval (2 : K)
            (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
              (A : K) (B : K) (C : K) (1 : K) Q R S) =
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S))
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
    have hS0 := degreeOneRaw_firstTwoZero_forcesThird hA hB h2 hQ0 hR0
    have h3K : (x3 : K) = 0 := h3aff.trans hS0
    have hx3 : x3 = 0 := by exact_mod_cast h3K
    exact ⟨h12.1, h12.2, hx3⟩
  · have hQ0 : (A : K) + Q = 0 := by
      rw [h13.1] at h1aff
      simpa using h1aff.symm
    have hS0 : (C : K) + S = 0 := by
      rw [h13.2] at h3aff
      simpa using h3aff.symm
    have hR0 := degreeOneRaw_firstThirdZero_forcesSecond hA hC h2 hQ0 hS0
    have h2K : (x2 : K) = 0 := h2aff.trans hR0
    have hx2 : x2 = 0 := by exact_mod_cast h2K
    exact ⟨h13.1, hx2, h13.2⟩
  · have hR0 : (B : K) + R = 0 := by
      rw [h23.1] at h2aff
      simpa using h2aff.symm
    have hS0 : (C : K) + S = 0 := by
      rw [h23.2] at h3aff
      simpa using h3aff.symm
    have hQ0 := degreeOneRaw_lastTwoZero_forcesFirst hB hC h2 hR0 hS0
    have h1K : (x1 : K) = 0 := h1aff.trans hQ0
    have hx1 : x1 = 0 := by exact_mod_cast h1K
    exact ⟨hx1, h23.1, h23.2⟩

/-- Packed state-free data for the degree-one unit-step terminal.  Packing the
certificate with its scalar parameters prevents downstream theorem application
from repeatedly normalising the long dependent certificate telescope. -/
structure DegreeOneTerminalEvalData (K : Type u) [Field K] [CharZero K] where
  A : ℕ
  B : ℕ
  C : ℕ
  Q : K
  R : K
  S : K
  phi : Polynomial K
  hA : 0 < A
  hB : 0 < B
  hC : 0 < C
  hphiDeg : phi.natDegree = 1
  hphi0 : phi.coeff 0 ≠ 0
  hcert : HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
    (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S

set_option maxHeartbeats 1000000 in
/-- Direct packed derivation of the single `rho = 2` relation needed by A19.91.
This bypasses both A19.90 wrapper theorems and the large combined
`exists_rankThreeAutonomousPolynomial_unit_linear_top_relation` package. -/
theorem DegreeOneTerminalEvalData.evalTwo
    [IsAlgClosed K]
    (D : DegreeOneTerminalEvalData K) :
    (-2 : K) *
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S) =
      Polynomial.eval (2 : K)
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (D.A : K) (D.B : K) (D.C : K) (1 : K) D.Q D.R D.S) := by
  have hphiPos : 0 < D.phi.natDegree := by
    rw [D.hphiDeg]
    norm_num
  rcases D.hcert with ⟨b, hb, hden, hidentity⟩
  have hdenNat : HC4.RationalRigidity.rankThreeTargetDenominator
      (D.A : K) (D.B : K) (D.C : K) ((1 : ℕ) : K) D.Q D.R D.S =
        Polynomial.C b := by
    simpa only [Nat.cast_one] using hden
  have hidentityNat :
      Polynomial.aeval (HC4.RationalRigidity.logarithmicSourceRatFunc D.phi)
          (HC4.RationalRigidity.rankThreeAutonomousPolynomial
            (D.A : K) (D.B : K) (D.C : K) ((1 : ℕ) : K)
            D.Q D.R D.S b) =
        HC4.RationalRigidity.logarithmicSourceEtaRatFunc D.phi := by
    simpa only [Nat.cast_one] using hidentity
  let T := HC4.RationalRigidity.rankThreeAutonomousPolynomial
    (D.A : K) (D.B : K) (D.C : K) ((1 : ℕ) : K) D.Q D.R D.S b

  have hdegT0 :=
    HC4.RationalRigidity.rankThreeAutonomousPolynomial_natDegree_le_two_of_certificate
      (K := K) (A := D.A) (B := D.B) (C := D.C) (P := 1)
      (Q := D.Q) (R := D.R) (S := D.S) (phi := D.phi)
      D.hA D.hB D.hC (by norm_num) hphiPos D.hphi0
      ⟨b, hb, hdenNat, hidentityNat⟩ b hb hdenNat hidentityNat
  have hdegT : T.natDegree ≤ 2 := by
    simpa [T] using hdegT0

  have hcoeff := HC4.RationalRigidity.rankThreeAutonomousPolynomial_coeff_zero_one
    (K := K) (A := D.A) (B := D.B) (C := D.C) (P := 1)
    (Q := D.Q) (R := D.R) (S := D.S) (b := b)
    D.hA D.hB D.hC (by norm_num) hb hdenNat
  have hT0 : T.coeff 0 = 0 := by
    simpa [T] using hcoeff.1
  have hT1 : T.coeff 1 = (1 : K) := by
    have hT1raw : T.coeff 1 = ((1 : ℕ) : K)⁻¹ := by
      simpa [T] using hcoeff.2
    simpa using hT1raw

  have hphi : D.phi ≠ 0 := by
    intro hz
    have hzeroDeg : D.phi.natDegree = 0 := by simp [hz]
    rw [D.hphiDeg] at hzeroDeg
    norm_num at hzeroDeg
  have hquad :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1) D.phi := by
    apply HC4.RationalRigidity.quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity
      hphi
    · exact hdegT
    · exact hT0
    · simpa [T] using hidentityNat
  have htop := HC4.Polynomial.quadraticAutonomous_top_relation
    (A := T.coeff 2) (B := T.coeff 1) hphiPos hquad
  rw [hT1] at htop

  have hT2 : T.coeff 2 = (-1 : K) := by
    have htop' : T.coeff 2 * (D.phi.natDegree : K) + 1 = 0 := by
      exact htop
    rw [D.hphiDeg] at htop'
    norm_num at htop' ⊢
    exact eq_neg_of_add_eq_zero_left htop'
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    HC4.RationalRigidity.eq_linear_add_quadratic_of_natDegree_le_two hdegT hT0
  have hTeval : Polynomial.eval (2 : K) T = (-2 : K) := by
    rw [hshape, hT1, hT2]
    norm_num

  have hraw :=
    HC4.RationalRigidity.rankThreeAutonomousPolynomial_mul_rawDenominator
      (K := K) (A := D.A) (B := D.B) (C := D.C) (P := 1)
      (Q := D.Q) (R := D.R) (S := D.S) (b := b)
      D.hA D.hB D.hC (by norm_num) hb hdenNat
  have hrawT :
      T * HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (D.A : K) (D.B : K) (D.C : K) ((1 : ℕ) : K)
          D.Q D.R D.S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (D.A : K) (D.B : K) (D.C : K) ((1 : ℕ) : K)
          D.Q D.R D.S := by
    simpa [T] using hraw
  have h2 := congrArg (Polynomial.eval (2 : K)) hrawT
  simp only [Polynomial.eval_mul] at h2
  rw [hTeval] at h2
  simpa only [Nat.cast_one] using h2

/-- State-free A19.91 adapter: construct the packed terminal once, derive the
single scalar relation, then finish by elementary codimension-two algebra. -/
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
  let D : DegreeOneTerminalEvalData K := {
    A := A
    B := B
    C := C
    Q := Q
    R := R
    S := S
    phi := phi
    hA := hA
    hB := hB
    hC := hC
    hphiDeg := hphiDeg
    hphi0 := hphi0
    hcert := hcert
  }
  have h2 := D.evalTwo
  exact degreeOneRaw_codimensionTwoPair_forcesAll
    hA hB hC h2 h1aff h2aff h3aff hpairs

end

end HC4.Valuation