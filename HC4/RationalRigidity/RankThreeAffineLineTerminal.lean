import HC4.Polynomial.RankThreeAffineMomentRealisation
import HC4.RationalRigidity.RankThreeEndpointNondegeneracy
import HC4.RationalRigidity.RankThreeInfinityAssembly
import Mathlib.Tactic

/-!
# A18.5.26: general honest affine rank-three edge to polynomial terminal

A18.5.25 removes the finite-segment divisibility restriction from the
multivariate moment bridge.  The remaining side conditions of the mature
rank-three infinity assembly depend only on the genuine endpoint and on the
one-variable coefficient polynomial.

Thus a general honest affine edge with positive rank-three endpoint,
positive omitted-coordinate step, nonconstant coefficient polynomial with
nonzero constant term, and zero Hessian determinant reaches the complete
polynomial autonomous terminal certificate.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **General affine rank-three line terminal theorem.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_affine_line
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : HC4.Polynomial.RankThreeAffineLineData A B C u1 q r s phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : HC4.Polynomial.hessianDeterminant L.polynomial = 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := phi)
      (A : K) (B : K) (C : K) (u1 : K) q r s := by
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hphi0
  have hcore := L.fractionCoreDetZero_of_hessian_zero hu1 hphi hdet
  have hRawD :=
    rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
      (K := K) (A := A) (B := B) (C := C) (P := u1)
      hA hB hC hu1 q r s
  have hSourceDegree :=
    logarithmicSourceDenominator_natDegree_pos_of_coeff_zero_ne_zero
      (K := K) phi hphiDeg hphi0
  exact hasRankThreePolynomialTerminalCertificate_of_core_det_zero
    hcore hRawD hSourceDegree

end

end HC4.RationalRigidity
