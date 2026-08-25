import HC4.RationalRigidity.RankThreeSingleDirectionRefinement
import HC4.RationalRigidity.RankThreeSupportedEdgeTerminal
import Mathlib.Tactic

/-!
# A18.5.53: supported single-direction refinement

A18.5.52 is stated in the field-valued affine direction.  On the honest finite
Newton line the directions are `u_i-v_i`, and both endpoint coefficients force
the extracted coefficient polynomial to have exact degree `M`.  This file
returns the refinement to integral endpoint geometry.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

private theorem supported_rankThree_terminal_data
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hM : 0 < M)
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F
    0 < phi.natDegree ∧ phi.coeff 0 ≠ 0 ∧
      HasRankThreePolynomialTerminalCertificate
        (phi := phi)
        (((M * v2 : ℕ) : K))
        (((M * v3 : ℕ) : K))
        (((M * v4 : ℕ) : K))
        (u1 : K)
        ((u2 : K) - (v2 : K))
        ((u3 : K) - (v3 : K))
        ((u4 : K) - (v4 : K)) := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    rw [coeff_zero_rankThreeLineCoefficientPolynomial]
    exact hstart
  have hphiM : phi.coeff M ≠ 0 := by
    dsimp [phi]
    rw [coeff_M_rankThreeLineCoefficientPolynomial]
    exact hend
  have hMle : M ≤ phi.natDegree :=
    Polynomial.le_natDegree_of_mem_supp M
      (Polynomial.mem_support_iff.mpr hphiM)
  have hphiDeg : 0 < phi.natDegree := by omega
  have hcert := hasRankThreePolynomialTerminalCertificate_of_supported_edge
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  exact ⟨hphiDeg, hphi0, hcert⟩

/-- If the second endpoint coordinate is unchanged, another transverse
coordinate is unchanged or the primitive direction preserves ordinary degree. -/
theorem supported_rankThree_edge_u2_eq_refines
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0)
    (hu2 : u2 = v2) :
    u3 = v3 ∨ u4 = v4 ∨
      1 + u2 + u3 + u4 = v2 + v3 + v4 := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  rcases supported_rankThree_terminal_data
      (K := K) hM hv2 hv3 hv4 hu1 hsupp hstart hend hdet with
    ⟨hphiDeg, hphi0, hcert⟩
  have hQ : (u2 : K) - (v2 : K) = 0 := by simp [hu2]
  rcases rankThree_terminal_Q_zero_refines
      (K := K)
      (A := M * v2) (B := M * v3) (C := M * v4) (P := u1)
      (Q := (u2 : K) - (v2 : K))
      (R := (u3 : K) - (v3 : K))
      (S := (u4 : K) - (v4 : K))
      (phi := phi)
      (Nat.mul_pos hM hv2) (Nat.mul_pos hM hv3) (Nat.mul_pos hM hv4)
      hu1 hphiDeg hphi0 hcert hQ with hR | hS | hsum
  · left
    have hc : (u3 : K) = (v3 : K) := sub_eq_zero.mp hR
    exact_mod_cast hc
  · right; left
    have hc : (u4 : K) = (v4 : K) := sub_eq_zero.mp hS
    exact_mod_cast hc
  · right; right
    have hf :
        (1 : K) + (u2 : K) + (u3 : K) + (u4 : K) =
          (v2 : K) + (v3 : K) + (v4 : K) := by
      rw [hu2]
      linear_combination hsum
    exact_mod_cast hf

/-- Cyclic supported refinement for the third coordinate. -/
theorem supported_rankThree_edge_u3_eq_refines
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0)
    (hu3 : u3 = v3) :
    u2 = v2 ∨ u4 = v4 ∨
      1 + u2 + u3 + u4 = v2 + v3 + v4 := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  rcases supported_rankThree_terminal_data
      (K := K) hM hv2 hv3 hv4 hu1 hsupp hstart hend hdet with
    ⟨hphiDeg, hphi0, hcert⟩
  have hR : (u3 : K) - (v3 : K) = 0 := by simp [hu3]
  rcases rankThree_terminal_R_zero_refines
      (K := K)
      (A := M * v2) (B := M * v3) (C := M * v4) (P := u1)
      (Q := (u2 : K) - (v2 : K))
      (R := (u3 : K) - (v3 : K))
      (S := (u4 : K) - (v4 : K))
      (phi := phi)
      (Nat.mul_pos hM hv2) (Nat.mul_pos hM hv3) (Nat.mul_pos hM hv4)
      hu1 hphiDeg hphi0 hcert hR with hQ | hS | hsum
  · left
    have hc : (u2 : K) = (v2 : K) := sub_eq_zero.mp hQ
    exact_mod_cast hc
  · right; left
    have hc : (u4 : K) = (v4 : K) := sub_eq_zero.mp hS
    exact_mod_cast hc
  · right; right
    have hf :
        (1 : K) + (u2 : K) + (u3 : K) + (u4 : K) =
          (v2 : K) + (v3 : K) + (v4 : K) := by
      rw [hu3]
      linear_combination hsum
    exact_mod_cast hf

/-- Cyclic supported refinement for the fourth coordinate. -/
theorem supported_rankThree_edge_u4_eq_refines
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend : MvPolynomial.coeff
      (rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : hessianDeterminant F = 0)
    (hu4 : u4 = v4) :
    u2 = v2 ∨ u3 = v3 ∨
      1 + u2 + u3 + u4 = v2 + v3 + v4 := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  rcases supported_rankThree_terminal_data
      (K := K) hM hv2 hv3 hv4 hu1 hsupp hstart hend hdet with
    ⟨hphiDeg, hphi0, hcert⟩
  have hS : (u4 : K) - (v4 : K) = 0 := by simp [hu4]
  rcases rankThree_terminal_S_zero_refines
      (K := K)
      (A := M * v2) (B := M * v3) (C := M * v4) (P := u1)
      (Q := (u2 : K) - (v2 : K))
      (R := (u3 : K) - (v3 : K))
      (S := (u4 : K) - (v4 : K))
      (phi := phi)
      (Nat.mul_pos hM hv2) (Nat.mul_pos hM hv3) (Nat.mul_pos hM hv4)
      hu1 hphiDeg hphi0 hcert hS with hQ | hR | hsum
  · left
    have hc : (u2 : K) = (v2 : K) := sub_eq_zero.mp hQ
    exact_mod_cast hc
  · right; left
    have hc : (u3 : K) = (v3 : K) := sub_eq_zero.mp hR
    exact_mod_cast hc
  · right; right
    have hf :
        (1 : K) + (u2 : K) + (u3 : K) + (u4 : K) =
          (v2 : K) + (v3 : K) + (v4 : K) := by
      rw [hu4]
      linear_combination hsum
    exact_mod_cast hf

end

end HC4.RationalRigidity
