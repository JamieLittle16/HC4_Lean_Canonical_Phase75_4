import HC4.Polynomial.RankThreeMvMomentRealisation
import HC4.RationalRigidity.RankThreeEndpointNondegeneracy
import HC4.RationalRigidity.RankThreeInfinityAssembly
import Mathlib.Tactic

/-!
# A18.5.9: honest rank-three exponent line to polynomial terminal certificate

A18.5.4--6 supplied the missing multivariate bridge from an honest finite
rank-three exponent line to the fraction-core determinant equation.  A18.5.8
shows that the two scalar side conditions used by the mature infinity assembly
are automatic from the endpoint geometry.

This file composes those ingredients.  It is the terminal theorem we wanted
on the rational-rigidity side of the A18 splice:

* the rank-three endpoint has three positive natural exponents;
* the opposite endpoint genuinely leaves the omitted coordinate;
* the one-variable coefficient polynomial has nonzero constant coefficient
  and positive degree;
* its degree lies inside the chosen finite segment;
* the resulting honest multivariate line has zero Hessian determinant.

Then the existing finite-pole and infinity machinery produces an honest
polynomial autonomous terminal certificate.  No raw rational denominator,
reduced source degree, or fraction-field hypothesis is supplied by the caller.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Honest rank-three line terminal theorem.**
A singular finite exponent line leaving a genuine rank-three endpoint carries
the complete polynomial autonomous terminal certificate. -/
theorem hasRankThreePolynomialTerminalCertificate_of_honest_line
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M)
    (hu1 : 0 < u1)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdeg : phi.natDegree ≤ M)
    (hdet : HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.rankThreeLinePolynomial
        v2 v3 v4 u1 u2 u3 u4 M phi) = 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := phi)
      (((M * v2 : ℕ) : K))
      (((M * v3 : ℕ) : K))
      (((M * v4 : ℕ) : K))
      (u1 : K)
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) := by
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hphi0
  have hcore :=
    HC4.Polynomial.rankThreeFractionCoreDetZero_of_line_hessianDeterminant_zero
      (K := K)
      (v2 := v2) (v3 := v3) (v4 := v4)
      (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
      (M := M) (phi := phi)
      hu1 hphi hdeg hdet
  have hMv2 : 0 < M * v2 := Nat.mul_pos hM hv2
  have hMv3 : 0 < M * v3 := Nat.mul_pos hM hv3
  have hMv4 : 0 < M * v4 := Nat.mul_pos hM hv4
  have hRawD :=
    rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
      (K := K)
      (A := M * v2) (B := M * v3) (C := M * v4) (P := u1)
      hMv2 hMv3 hMv4 hu1
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K))
  have hSourceDegree :=
    logarithmicSourceDenominator_natDegree_pos_of_coeff_zero_ne_zero
      (K := K) phi hphiDeg hphi0
  exact hasRankThreePolynomialTerminalCertificate_of_core_det_zero
    hcore hRawD hSourceDegree

end

end HC4.RationalRigidity
