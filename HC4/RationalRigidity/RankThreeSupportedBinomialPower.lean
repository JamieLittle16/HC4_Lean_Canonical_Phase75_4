import HC4.RationalRigidity.RankThreeSupportedEdgeTerminal
import HC4.RationalRigidity.RankThreeUnshiftedBinomialForm
import Mathlib.Tactic

/-!
# A18.5.58: the actual supported terminal has full binomial coefficient profile

The autonomous-rigidity stack already proves that a genuine rank-three
terminal coefficient polynomial is a scalar multiple of one binomial power.
For an actual supported edge the coefficient at the far endpoint `j = M` is
nonzero, while the extracted coefficient polynomial has degree at most `M`.
Hence its natural degree is exactly `M`.

Therefore the coefficient polynomial extracted from the actual multivariate
edge has the exact form

    c * (X - alpha)^M,

with both `c` and `alpha` nonzero.  This is the lossless coefficient profile
needed to reconstruct the terminal as a power of one multivariate binomial.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Full binomial profile on an actual supported rank-three terminal.** -/
theorem supported_rankThree_edge_coefficientPolynomial_eq_binomial_power
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
    (hdet : hessianDeterminant F = 0) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 M F
    ∃ alpha c : K,
      alpha ≠ 0 ∧ c ≠ 0 ∧
      phi = Polynomial.C c *
        (Polynomial.X - Polynomial.C alpha) ^ M := by
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
  have hdegGe : M ≤ phi.natDegree := by
    exact Polynomial.le_natDegree_of_mem_supp M
      (Polynomial.mem_support_iff.mpr hphiM)
  have hdegEq : phi.natDegree = M := Nat.le_antisymm hdegLe hdegGe
  have hphiDeg : 0 < phi.natDegree := by omega

  have hcert := hasRankThreePolynomialTerminalCertificate_of_supported_edge
    (K := K) hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  rcases exists_rankThree_translated_pure_power
      (K := K)
      (Nat.mul_pos hM hv2)
      (Nat.mul_pos hM hv3)
      (Nat.mul_pos hM hv4)
      hu1 hphiDeg hphi0 hcert with
    ⟨alpha, c, halpha, hc, hpure⟩
  have hunshift := eq_binomial_power_of_translate_eq_pure_power hpure
  rw [hdegEq] at hunshift
  exact ⟨alpha, c, halpha, hc, hunshift⟩

end

end HC4.RationalRigidity
