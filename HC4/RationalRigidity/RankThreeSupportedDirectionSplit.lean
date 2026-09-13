import HC4.RationalRigidity.RankThreeSupportedEdgeTerminal
import HC4.RationalRigidity.RankThreeTerminalDirectionSplit
import Mathlib.Tactic

/-!
# A18.5.45: finite terminal direction split on the actual supported edge

A18.5.42 gives the final scalar rank-three split in the affine coordinates

    Q = u2-v2,  R = u3-v3,  S = u4-v4.

For the honest finite Newton edge, both endpoint coefficients are nonzero, so
the extracted coefficient polynomial has degree exactly the segment length
`M`.  Characteristic zero then turns the scalar alternatives back into exact
integral geometry:

* `M = 1`;
* `u2 = v2`, `u3 = v3`, or `u4 = v4`;
* or the primitive affine direction preserves ordinary degree,

      1 + u2 + u3 + u4 = v2 + v3 + v4.

This is the caller-facing finite split needed by the terminal pencil/restart
dispatch; no rational-function data remains in its conclusion.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Actual supported rank-three terminal direction split.** -/
theorem supported_rankThree_edge_degreeOne_or_directionDegenerate
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
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
    M = 1 ∨
      u2 = v2 ∨ u3 = v3 ∨ u4 = v4 ∨
      1 + u2 + u3 + u4 = v2 + v3 + v4 := by
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
  have hdegLe : phi.natDegree ≤ M := by
    dsimp [phi]
    exact rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 u1 u2 u3 u4 M F
  have hMle : M ≤ phi.natDegree :=
    Polynomial.le_natDegree_of_mem_supp M
      (Polynomial.mem_support_iff.mpr hphiM)
  have hdeg : phi.natDegree = M := Nat.le_antisymm hdegLe hMle
  have hphiDeg : 0 < phi.natDegree := by omega

  have hcert := hasRankThreePolynomialTerminalCertificate_of_supported_edge
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  have hsplit := rankThree_terminal_degreeOne_or_directionDegenerate
    (K := K)
    (A := M * v2) (B := M * v3) (C := M * v4)
    (P := u1)
    (Q := (u2 : K) - (v2 : K))
    (R := (u3 : K) - (v3 : K))
    (S := (u4 : K) - (v4 : K))
    (phi := phi)
    (Nat.mul_pos hM hv2) (Nat.mul_pos hM hv3) (Nat.mul_pos hM hv4)
    hu1 hphiDeg hphi0 hcert

  rcases hsplit with hD | hQ | hR | hS | hsum
  · left
    omega
  · right; left
    have hcast : (u2 : K) = (v2 : K) := sub_eq_zero.mp hQ
    exact_mod_cast hcast
  · right; right; left
    have hcast : (u3 : K) = (v3 : K) := sub_eq_zero.mp hR
    exact_mod_cast hcast
  · right; right; right; left
    have hcast : (u4 : K) = (v4 : K) := sub_eq_zero.mp hS
    exact_mod_cast hcast
  · right; right; right; right
    have hfield :
        (1 : K) + (u2 : K) + (u3 : K) + (u4 : K) =
          (v2 : K) + (v3 : K) + (v4 : K) := by
      linear_combination hsum
    exact_mod_cast hfield

end

end HC4.RationalRigidity
