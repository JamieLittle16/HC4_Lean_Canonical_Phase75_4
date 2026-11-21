import HC4.Polynomial.RankThreeLineReconstruction
import HC4.RationalRigidity.RankThreeHonestLineTerminal
import Mathlib.Tactic

/-!
# A18.5.23: an actual Newton rank-three edge reaches the terminal ODE

The rational-rigidity theorem A18.5.9 is phrased using the canonical
`rankThreeLinePolynomial`.  A18.5.22 now proves that an actual multivariate
polynomial supported on the corresponding finite affine line is literally
that object for its canonically extracted coefficient polynomial.

This file removes the remaining caller-visible univariate data.  If the two
endpoints of a genuine rank-three support edge occur with nonzero coefficient,
the extracted polynomial automatically has nonzero constant term, positive
degree and degree at most `M`.  Zero Hessian of the actual edge therefore
feeds directly into the complete rank-three polynomial terminal certificate.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Actual supported rank-three edge -> polynomial autonomous terminal.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_supported_edge
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M)
    (hu1 : 0 < u1)
    (hsupp : HC4.Polynomial.IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F)
    (hstart :
      MvPolynomial.coeff
        (HC4.Polynomial.rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0) F ≠ 0)
    (hend :
      MvPolynomial.coeff
        (HC4.Polynomial.rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M) F ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant F = 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
        v2 v3 v4 u1 u2 u3 u4 M F)
      (((M * v2 : ℕ) : K))
      (((M * v3 : ℕ) : K))
      (((M * v4 : ℕ) : K))
      (u1 : K)
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) := by
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

  have hphiDeg : 0 < phi.natDegree := by
    have hmem : M ∈ phi.support := Polynomial.mem_support_iff.mpr hphiM
    have hle : M ≤ phi.natDegree := Polynomial.le_natDegree_of_mem_supp M hmem
    omega

  have hdeg : phi.natDegree ≤ M := by
    dsimp [phi]
    exact HC4.Polynomial.rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 u1 u2 u3 u4 M F

  have hline :
      F = HC4.Polynomial.rankThreeLinePolynomial
        v2 v3 v4 u1 u2 u3 u4 M phi := by
    dsimp [phi]
    exact HC4.Polynomial.eq_rankThreeLinePolynomial_of_supported hu1 hsupp

  have hdetLine :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeLinePolynomial
          v2 v3 v4 u1 u2 u3 u4 M phi) = 0 := by
    rw [← hline]
    exact hdet

  exact hasRankThreePolynomialTerminalCertificate_of_honest_line
    hv2 hv3 hv4 hM hu1 hphiDeg hphi0 hdeg hdetLine

end

end HC4.RationalRigidity
