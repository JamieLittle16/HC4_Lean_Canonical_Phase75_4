import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import HC4.RationalRigidity.RankThreeTranslatedPurePower
import HC4.RationalRigidity.RankThreeUnitLongitudinalStep
import Mathlib.Tactic

/-!
# A18.5.39: terminal rank-three binomial normal form

The preceding rank-three stack has now reached the exact endpoint needed by
`HC4.Polynomial.RankThreePencils`.

For an honest affine rank-three line with positive initial transverse
coordinates and singular Hessian, the terminal certificate simultaneously
forces:

* primitive omitted-coordinate step `u1 = 1`;
* a genuine first coefficient layer `phi.coeff 1 != 0`;
* the far supported exponent onto the toric boundary; and
* after translation to a nonzero root, the whole coefficient polynomial to be
  a nonzero scalar multiple of `X^D`.

Keeping these facts in one structure avoids repeatedly reopening the rational
ODE package in the final pencil dispatch.  This is a data-preserving adapter:
no additional geometric assumption is introduced.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Exact normal-form data left by a genuine affine rank-three terminal. -/
structure RankThreeTerminalBinomialNormalForm
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi) where
  omitted_step_eq_one : u1 = 1
  first_coefficient_ne_zero : phi.coeff 1 ≠ 0
  top_exponent_on_boundary : MvExponentOnBoundary (L.exponent phi.natDegree)
  root : K
  scalar : K
  root_ne_zero : root ≠ 0
  scalar_ne_zero : scalar ≠ 0
  translated_eq_pure_power :
    HC4.Polynomial.translatePolynomial root phi =
      Polynomial.C scalar * Polynomial.X ^ phi.natDegree

/-- **Terminal binomial normal-form package.**

A singular honest affine rank-three line satisfying the genuine positive
endpoint hypotheses canonically reaches the primitive boundary-to-boundary
pure-power package consumed by the final rank-three pencil cases. -/
theorem rankThreeTerminal_binomialNormalForm
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    RankThreeTerminalBinomialNormalForm L := by
  have hcert := hasRankThreePolynomialTerminalCertificate_of_affine_line
    L hA hB hC hu1 hphiDeg hphi0 hdet
  have hstep := rankThree_unit_longitudinal_step_of_certificate
    hA hB hC hu1 hphiDeg hphi0 hcert
  have hboundary := rankThreeAffineLine_topExponent_on_boundary_of_certificate
    L hA hB hC hu1 hphiDeg hphi0 hcert
  rcases exists_rankThree_translated_pure_power
      hA hB hC hu1 hphiDeg hphi0 hcert with
    ⟨alpha, c, halpha, hc, hpure⟩
  exact {
    omitted_step_eq_one := hstep.1
    first_coefficient_ne_zero := hstep.2
    top_exponent_on_boundary := hboundary
    root := alpha
    scalar := c
    root_ne_zero := halpha
    scalar_ne_zero := hc
    translated_eq_pure_power := hpure
  }

end

end HC4.RationalRigidity
