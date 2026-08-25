import HC4.RationalRigidity.RankThreeHomogeneousOtherFixedRelations
import Mathlib.Tactic

/-!
# A18.5.62: the surviving homogeneous endpoint has a unit missing direction

A18.5.56 leaves only `sp` and `rq` far endpoints.  A18.5.59 says that one
transverse direction is fixed, and A18.5.60--61 give the next autonomous
coefficient relation in each fixed-direction branch.

For an `sp` endpoint the third endpoint coordinate is zero, so its direction
coefficient is `-v3`.  The fixed-direction relations force `v3 = 1`.
Symmetrically, at an `rq` endpoint they force `v4 = 1`.

These unit equalities are the final arithmetic input needed to turn ordinary
homogeneity into a second fixed transverse direction.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- `sp` homogeneous endpoint forces the starting third coordinate to be one. -/
theorem supported_balanced_rankThree_homogeneous_sp_forces_v3_one
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
    (hdet : HC4.Polynomial.hessianDeterminant F = 0)
    (hsp : 0 < u2 ∧ u3 = 0 ∧ 0 < u4) :
    v3 = 1 := by
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
  have hfixed :=
    supported_balanced_rankThree_homogeneous_direction_has_fixed_transverse
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet

  have hApos : 0 < M * v2 := Nat.mul_pos hM hv2
  have hBpos : 0 < M * v3 := Nat.mul_pos hM hv3
  have hCpos : 0 < M * v4 := Nat.mul_pos hM hv4
  have hAne : (((M * v2 : ℕ) : K)) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hApos
  have hCne : (((M * v4 : ℕ) : K)) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hCpos
  have hbaseOne :
      ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) +
          ((M * v4 : ℕ) : K) - 1 ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) +
          ((M * v4 : ℕ) : K) = 1 := sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v3 + M * v4 = 1 := by exact_mod_cast heqK
    omega
  have htailBC :
      ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) - (M : K) ≠ 0 := by
    intro hz
    have heqK :
        ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) = (M : K) :=
      sub_eq_zero.mp hz
    have heqNat : M * v3 + M * v4 = M := by exact_mod_cast heqK
    have hv3one : 1 ≤ v3 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv3)
    have hv4one : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
    have hMv3 : M ≤ M * v3 := by simpa using Nat.mul_le_mul_left M hv3one
    have hMv4 : M ≤ M * v4 := by simpa using Nat.mul_le_mul_left M hv4one
    omega
  have htailAB :
      ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) - (M : K) ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) = (M : K) :=
      sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v3 = M := by exact_mod_cast heqK
    have hv2one : 1 ≤ v2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv2)
    have hv3one : 1 ≤ v3 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv3)
    have hMv2 : M ≤ M * v2 := by simpa using Nat.mul_le_mul_left M hv2one
    have hMv3 : M ≤ M * v3 := by simpa using Nat.mul_le_mul_left M hv3one
    omega

  rcases hfixed with hu2eq | hu3eq | hu4eq
  · have hQ : ((u2 : K) - (v2 : K)) = 0 := by rw [hu2eq]; ring
    have hRne : ((u3 : K) - (v3 : K)) ≠ 0 := by
      rw [hsp.2.1]
      simp only [Nat.cast_zero, zero_sub, neg_ne_zero]
      exact_mod_cast Nat.ne_of_gt hv3
    have hrel := rankThree_terminal_homogeneous_Q_zero_relation
      (K := K) hApos hBpos hCpos hu1 hphiDeg hphi0 hcert hsum hQ
    rw [hdegEq] at hrel
    have h4 := (mul_eq_zero.mp hrel).resolve_right htailBC
    have h3 := (mul_eq_zero.mp h4).resolve_right hbaseOne
    have hRp1 : ((u3 : K) - (v3 : K)) + 1 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hAne hRne)
    rw [hsp.2.1] at hRp1
    have hv3K : (v3 : K) = 1 := by linear_combination hRp1
    exact_mod_cast hv3K
  · rw [hsp.2.1] at hu3eq
    omega
  · have hS : ((u4 : K) - (v4 : K)) = 0 := by rw [hu4eq]; ring
    have hRform : ((u3 : K) - (v3 : K)) = -(v3 : K) := by
      rw [hsp.2.1]
      ring
    have hQp1 : ((u2 : K) - (v2 : K)) + 1 = (v3 : K) := by
      linear_combination hsum
    have hQp1ne : ((u2 : K) - (v2 : K)) + 1 ≠ 0 := by
      rw [hQp1]
      exact_mod_cast Nat.ne_of_gt hv3
    have hrel := rankThree_terminal_homogeneous_S_zero_relation
      (K := K) hApos hBpos hCpos hu1 hphiDeg hphi0 hcert hsum hS
    rw [hdegEq] at hrel
    have h4 := (mul_eq_zero.mp hrel).resolve_right htailAB
    have h3 := (mul_eq_zero.mp h4).resolve_right hbaseOne
    have hCQ := (mul_eq_zero.mp h3).resolve_right hQp1ne
    have hQ : ((u2 : K) - (v2 : K)) = 0 :=
      (mul_eq_zero.mp hCQ).resolve_left hCne
    rw [hQ] at hsum
    rw [hS, hRform] at hsum
    have hv3K : (v3 : K) = 1 := by linear_combination hsum
    exact_mod_cast hv3K

/-- `rq` homogeneous endpoint forces the starting fourth coordinate to be one. -/
theorem supported_balanced_rankThree_homogeneous_rq_forces_v4_one
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
    (hdet : HC4.Polynomial.hessianDeterminant F = 0)
    (hrq : 0 < u2 ∧ 0 < u3 ∧ u4 = 0) :
    v4 = 1 := by
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
  have hfixed :=
    supported_balanced_rankThree_homogeneous_direction_has_fixed_transverse
      (K := K) ha hb hv2 hv3 hv4 hM hu1 hbalanced
      hsupp hstart hend hdet

  have hApos : 0 < M * v2 := Nat.mul_pos hM hv2
  have hBpos : 0 < M * v3 := Nat.mul_pos hM hv3
  have hCpos : 0 < M * v4 := Nat.mul_pos hM hv4
  have hBne : (((M * v3 : ℕ) : K)) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hBpos
  have hbaseOne :
      ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) +
          ((M * v4 : ℕ) : K) - 1 ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v3 : ℕ) : K) +
          ((M * v4 : ℕ) : K) = 1 := sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v3 + M * v4 = 1 := by exact_mod_cast heqK
    omega
  have htailBC :
      ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) - (M : K) ≠ 0 := by
    intro hz
    have heqK :
        ((M * v3 : ℕ) : K) + ((M * v4 : ℕ) : K) = (M : K) :=
      sub_eq_zero.mp hz
    have heqNat : M * v3 + M * v4 = M := by exact_mod_cast heqK
    have hv3one : 1 ≤ v3 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv3)
    have hv4one : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
    have hMv3 : M ≤ M * v3 := by simpa using Nat.mul_le_mul_left M hv3one
    have hMv4 : M ≤ M * v4 := by simpa using Nat.mul_le_mul_left M hv4one
    omega
  have htailAC :
      ((M * v2 : ℕ) : K) + ((M * v4 : ℕ) : K) - (M : K) ≠ 0 := by
    intro hz
    have heqK :
        ((M * v2 : ℕ) : K) + ((M * v4 : ℕ) : K) = (M : K) :=
      sub_eq_zero.mp hz
    have heqNat : M * v2 + M * v4 = M := by exact_mod_cast heqK
    have hv2one : 1 ≤ v2 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv2)
    have hv4one : 1 ≤ v4 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv4)
    have hMv2 : M ≤ M * v2 := by simpa using Nat.mul_le_mul_left M hv2one
    have hMv4 : M ≤ M * v4 := by simpa using Nat.mul_le_mul_left M hv4one
    omega

  rcases hfixed with hu2eq | hu3eq | hu4eq
  · have hQ : ((u2 : K) - (v2 : K)) = 0 := by rw [hu2eq]; ring
    have hSform : ((u4 : K) - (v4 : K)) = -(v4 : K) := by
      rw [hrq.2.2]
      ring
    have hRp1 : ((u3 : K) - (v3 : K)) + 1 = (v4 : K) := by
      linear_combination hsum
    have hRp1ne : ((u3 : K) - (v3 : K)) + 1 ≠ 0 := by
      rw [hRp1]
      exact_mod_cast Nat.ne_of_gt hv4
    have hrel := rankThree_terminal_homogeneous_Q_zero_relation
      (K := K) hApos hBpos hCpos hu1 hphiDeg hphi0 hcert hsum hQ
    rw [hdegEq] at hrel
    have h4 := (mul_eq_zero.mp hrel).resolve_right htailBC
    have h3 := (mul_eq_zero.mp h4).resolve_right hbaseOne
    have hAR := (mul_eq_zero.mp h3).resolve_right hRp1ne
    have hR : ((u3 : K) - (v3 : K)) = 0 :=
      (mul_eq_zero.mp hAR).resolve_left (by
        exact_mod_cast Nat.ne_of_gt hApos)
    rw [hQ, hR, hSform] at hsum
    have hv4K : (v4 : K) = 1 := by linear_combination hsum
    exact_mod_cast hv4K
  · have hR : ((u3 : K) - (v3 : K)) = 0 := by rw [hu3eq]; ring
    have hSform : ((u4 : K) - (v4 : K)) = -(v4 : K) := by
      rw [hrq.2.2]
      ring
    have hQp1 : ((u2 : K) - (v2 : K)) + 1 = (v4 : K) := by
      linear_combination hsum
    have hQp1ne : ((u2 : K) - (v2 : K)) + 1 ≠ 0 := by
      rw [hQp1]
      exact_mod_cast Nat.ne_of_gt hv4
    have hrel := rankThree_terminal_homogeneous_R_zero_relation
      (K := K) hApos hBpos hCpos hu1 hphiDeg hphi0 hcert hsum hR
    rw [hdegEq] at hrel
    have h4 := (mul_eq_zero.mp hrel).resolve_right htailAC
    have h3 := (mul_eq_zero.mp h4).resolve_right hbaseOne
    have hBQ := (mul_eq_zero.mp h3).resolve_right hQp1ne
    have hQ : ((u2 : K) - (v2 : K)) = 0 :=
      (mul_eq_zero.mp hBQ).resolve_left hBne
    rw [hQ, hR, hSform] at hsum
    have hv4K : (v4 : K) = 1 := by linear_combination hsum
    exact_mod_cast hv4K
  · rw [hrq.2.2] at hu4eq
    omega

end

end HC4.RationalRigidity
