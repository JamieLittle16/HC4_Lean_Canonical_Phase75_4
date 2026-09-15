import HC4.Polynomial.RankThreeVerticalMomentRealisation
import HC4.RationalRigidity.RankThreeEndpointNondegeneracy
import HC4.RationalRigidity.RankThreeInfinityAssembly
import Mathlib.Tactic

/-!
# A18.5.12: vertical rank-three line terminal certificate

The stationary Smith source fibre has the native form

    x₁^b x₂^c x₃^d φ(x₀).

A18.5.11 turns zero Hessian determinant of this honest multivariate polynomial
into the mature rank-three fraction-core equation with direction
`(1,0,0,0)`.  A18.5.8 discharges the two remaining rational side conditions
from the geometric endpoint hypotheses `b,c,d > 0`, positive degree of `φ`,
and nonzero constant coefficient.

Thus no auxiliary segment length, denominator assumption, or cocharacter is
required for the vertical terminal route.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Honest vertical line gives the full polynomial rank-three terminal
certificate.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_vertical_line
    [IsAlgClosed K]
    {b c d : ℕ}
    {phi : Polynomial K}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdeg : 0 < phi.natDegree)
    (hconst : phi.coeff 0 ≠ 0)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial b c d phi) = 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := phi) (b : K) (c : K) (d : K) 1 0 0 0 := by
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hconst
  have hcore :
      HC4.Polynomial.RankThreeFractionCoreDetZero
        phi (b : K) (c : K) (d : K) 1 0 0 0 :=
    HC4.Polynomial.rankThreeFractionCoreDetZero_of_vertical_hessianDeterminant_zero
      hphi hdet
  have hraw :
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        (b : K) (c : K) (d : K) 1 0 0 0 ≠ 0 := by
    simpa using
      rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
        (K := K) hb hc hd (by decide : 0 < (1 : ℕ))
        (0 : K) (0 : K) (0 : K)
  have hsource :
      0 < (logarithmicSourceDenominator phi).natDegree :=
    logarithmicSourceDenominator_natDegree_pos_of_coeff_zero_ne_zero
      phi hdeg hconst
  exact
    hasRankThreePolynomialTerminalCertificate_of_core_det_zero
      hcore hraw hsource

end

end HC4.RationalRigidity
