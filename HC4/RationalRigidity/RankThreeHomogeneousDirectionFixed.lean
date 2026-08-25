import HC4.RationalRigidity.RankThreeBalancedHomogeneousEndpointFacet
import HC4.RationalRigidity.RankThreeHighestDirectionRelation
import Mathlib.Tactic

/-!
# A18.5.59: homogeneous rank-three terminals have a fixed transverse direction

A18.5.41 used the highest target coefficient.  In the surviving homogeneous
case that coefficient vanishes identically because

    1 + Q + R + S = 0.

The next coefficient is still informative.  Writing

    Sigma0 = A + B + C,
    D = natDegree phi,

and using the already-proved quadratic target

    T(rho) = rho + t2 rho^2,     t2 * D + 1 = 0,

coefficient four of `T * D_raw = N_raw` gives

    Q R S (Sigma0 - 1) (Sigma0 - D) = 0.

For an actual supported rank-three segment, `A=M v2`, `B=M v3`, `C=M v4`
and `D=M`.  Positivity of `M,v2,v3,v4` excludes both scalar factors.  Hence
one of `Q,R,S` vanishes: one transverse coordinate is unchanged along the
homogeneous terminal edge.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Quartic raw-numerator coefficient after the primitive direction becomes
ordinary-degree preserving. -/
set_option maxHeartbeats 4000000 in
theorem coeff_four_rankThreeEtaNumeratorPolynomial_unit_of_direction_sum_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      A B C 1 Q R S).coeff 4 =
      -(Q * R * S * (A + B + C - 1)) := by
  have hS : S = -(1 + Q + R) := by
    linear_combination hsum
  rw [hS]
  simp [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
    HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_mul]
  ring

/-- Quadratic raw-denominator coefficient in the same homogeneous direction. -/
set_option maxHeartbeats 6000000 in
theorem coeff_two_rankThreeEtaDenominatorPolynomial_unit_of_direction_sum_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 2 =
      Q * R * S * (A + B + C) * (A + B + C - 1) := by
  have hS : S = -(1 + Q + R) := by
    linear_combination hsum
  rw [hS]
  simp [HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
    HC4.Polynomial.rankThreeEtaDenominator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    HC4.Polynomial.rankThreeWeightedCofactorSum,
    HC4.Polynomial.rankThreeDirectionDefect,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_mul]
  ring

/-- **Second homogeneous terminal relation.**
The first coefficient below the vanished highest-direction coefficient forces
one transverse direction factor unless the base degree is `1` or equals the
source degree. -/
theorem rankThree_terminal_homogeneous_direction_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hsum : 1 + Q + R + S = 0) :
    Q * R * S *
        ((A : K) + (B : K) + (C : K) - 1) *
        ((A : K) + (B : K) + (C : K) - (phi.natDegree : K)) = 0 := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, hidentity, hdegT, hT0, hT1, htop⟩
  subst P

  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S

  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hD3 : Draw.coeff 3 = 0 := by
    have h := coeff_three_rankThreeEtaDenominatorPolynomial_unit
      (A : K) (B : K) (C : K) Q R S
    rw [hsum] at h
    simpa [Draw] using h
  have hD2 :
      Draw.coeff 2 =
        Q * R * S *
          ((A : K) + (B : K) + (C : K)) *
          ((A : K) + (B : K) + (C : K) - 1) := by
    simpa [Draw] using
      coeff_two_rankThreeEtaDenominatorPolynomial_unit_of_direction_sum_zero
        (A : K) (B : K) (C : K) Q R S hsum
  have hN4 :
      Nraw.coeff 4 =
        -(Q * R * S *
          ((A : K) + (B : K) + (C : K) - 1)) := by
    simpa [Nraw] using
      coeff_four_rankThreeEtaNumeratorPolynomial_unit_of_direction_sum_zero
        (A : K) (B : K) (C : K) Q R S hsum

  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 4) hraw
  rw [hshape] at hcoeff
  simp only [Polynomial.add_mul, Polynomial.coeff_add,
    Polynomial.coeff_mul_X, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul] at hcoeff
  rw [hD3, hD2, hN4, hT1'] at hcoeff

  linear_combination
    -((phi.natDegree : K)) * hcoeff +
      (Q * R * S *
        ((A : K) + (B : K) + (C : K)) *
        ((A : K) + (B : K) + (C : K) - 1)) * htop'

/-- **Actual homogeneous edge has a fixed transverse coordinate.** -/
theorem supported_balanced_rankThree_homogeneous_direction_has_fixed_transverse
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HC4.Polynomial.HasBalancedMvSupport a b F)
    (hsupp : HC4.Polynomial.IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (HC4.Polynomial.rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (HC4.Polynomial.rankThreeLineExponentFinsupp
        v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant F = 0) :
    u2 = v2 ∨ u3 = v3 ∨ u4 = v4 := by
  let phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    rw [HC4.Polynomial.coeff_zero_rankThreeLineCoefficientPolynomial]
    exact hstart
  have hphiM : phi.coeff M ≠ 0 := by
    dsimp [phi]
    rw [HC4.Polynomial.coeff_M_rankThreeLineCoefficientPolynomial]
    exact hend
  have hdegLe : phi.natDegree ≤ M := by
    dsimp [phi]
    exact HC4.Polynomial.rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 u1 u2 u3 u4 M F
  have hdegGe : M ≤ phi.natDegree :=
    Polynomial.le_natDegree_of_mem_supp M
      (Polynomial.mem_support_iff.mpr hphiM)
  have hdegEq : phi.natDegree = M := Nat.le_antisymm hdegLe hdegGe
  have hphiDeg : 0 < phi.natDegree := by omega

  have hdegree := supported_balanced_rankThree_edge_ordinaryDegreePreserving
    (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
    hsupp hstart hend hdet
  have hdegreeK :
      (1 : K) + (u2 : K) + (u3 : K) + (u4 : K) =
        (v2 : K) + (v3 : K) + (v4 : K) := by
    exact_mod_cast hdegree
  have hsum :
      (1 : K) + ((u2 : K) - (v2 : K)) +
        ((u3 : K) - (v3 : K)) + ((u4 : K) - (v4 : K)) = 0 := by
    linear_combination hdegreeK

  have hcert := hasRankThreePolynomialTerminalCertificate_of_supported_edge
    (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  have hrel := rankThree_terminal_homogeneous_direction_relation
    (K := K)
    (Nat.mul_pos hM hv2) (Nat.mul_pos hM hv3) (Nat.mul_pos hM hv4)
    hu1 hphiDeg hphi0 hcert hsum
  rw [hdegEq] at hrel

  have hMv2 : M ≤ M * v2 := by
    have hv : 1 ≤ v2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv2)
    simpa using Nat.mul_le_mul_left M hv
  have hMv3 : M ≤ M * v3 := by
    have hv : 1 ≤ v3 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv3)
    simpa using Nat.mul_le_mul_left M hv
  have hMv4 : M ≤ M * v4 := by
    have hv : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
    simpa using Nat.mul_le_mul_left M hv
  have hsumNatOne : 1 < M * v2 + M * v3 + M * v4 := by omega
  have hsumNatM : M < M * v2 + M * v3 + M * v4 := by omega

  have hbaseOne :
      ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) - 1 ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) = 1 :=
      sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v3 + M * v4 = 1 := by
      exact_mod_cast heqK
    omega
  have hbaseDegree :
      ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) - (M : K) ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) = (M : K) :=
      sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v3 + M * v4 = M := by
      exact_mod_cast heqK
    omega

  have hqrs :
      (((u2 : K) - (v2 : K)) * ((u3 : K) - (v3 : K)) *
        ((u4 : K) - (v4 : K))) = 0 := by
    rcases mul_eq_zero.mp hrel with hleft | hdeg
    · rcases mul_eq_zero.mp hleft with hqrs | hone
      · exact hqrs
      · exact (hbaseOne hone).elim
    · exact (hbaseDegree hdeg).elim

  rcases mul_eq_zero.mp hqrs with hqr | hS
  · rcases mul_eq_zero.mp hqr with hQ | hR
    · left
      exact_mod_cast sub_eq_zero.mp hQ
    · right
      left
      exact_mod_cast sub_eq_zero.mp hR
  · right
    right
    exact_mod_cast sub_eq_zero.mp hS

end

end HC4.RationalRigidity
