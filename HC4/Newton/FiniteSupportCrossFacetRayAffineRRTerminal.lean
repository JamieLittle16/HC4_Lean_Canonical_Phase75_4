import HC4.Newton.FiniteSupportCrossFacetRayAffineRR
import HC4.Newton.MvBoundaryStrata
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import Mathlib.Tactic

/-!
# A19.72: a balance-free `qs` ray reaches the general affine RR terminal

A19.67 extracts an honest affine support ray without torus balance.  The
existing A19.69 affine-realisation module reindexes a ray with contact
coordinate `0` by that literal coordinate and reconstructs its polynomial
exactly as a `RankThreeAffineLineData`, with primitive omitted-coordinate step
one, nonzero constant coefficient, positive coefficient degree, and exact
Hessian-singularity transport.

If the retained facet endpoint is rank three on `.qs`, its three transverse
coordinates are strictly positive.  These are exactly the remaining endpoint
hypotheses of the mature general affine RationalRigidity entry theorem.

Thus a balance-free `qs` ray already carries a complete
`HasRankThreePolynomialTerminalCertificate`.  No torus balance, integrality of
transverse slopes, finite-segment divisibility, or new terminal algebra is
introduced here.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Balance-free ray to affine RationalRigidity terminal.**

A genuine singular cross-facet ray in the canonical contact chart whose facet
endpoint is rank three on `.qs` satisfies the complete general affine terminal
certificate. -/
theorem CrossFacetRayData.zero_rankThree_terminalCertificate
    {F : MvPolynomial (Fin 4) K}
    (R : CrossFacetRayData F (0 : Fin 4))
    (hzero : hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs R.facetExponent) :
    HasRankThreePolynomialTerminalCertificate
      (phi := R.zeroCoefficientPolynomial)
      ((R.facetExponent 1 : ℕ) : K)
      ((R.facetExponent 2 : ℕ) : K)
      ((R.facetExponent 3 : ℕ) : K)
      (1 : K)
      (R.zeroSlope (1 : Fin 4))
      (R.zeroSlope (2 : Fin 4))
      (R.zeroSlope (3 : Fin 4)) := by
  have hcoords := mvRankThreeOnFacet_qs hthree
  exact hasRankThreePolynomialTerminalCertificate_of_affine_line
    R.zeroAffineLineData
    hcoords.2.1
    hcoords.2.2.1
    hcoords.2.2.2
    (by norm_num)
    R.zeroCoefficientPolynomial_natDegree_pos
    R.zeroCoefficientPolynomial_coeff_zero_ne
    (R.zeroAffineLineData_hessian_zero hzero)

end

end HC4.Newton
