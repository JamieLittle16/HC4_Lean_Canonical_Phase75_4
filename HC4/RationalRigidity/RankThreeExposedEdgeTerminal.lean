import HC4.RationalRigidity.RankThreeSupportedEdgeTerminal
import HC4.Polynomial.MaximalHessianInitial
import Mathlib.Tactic

/-!
# A18.5.24: exposed rank-three edges inherit singularity automatically

A18.5.23 consumes an actual polynomial already known to be supported on one
finite rank-three line and to have zero Hessian determinant.  In the Newton
application that polynomial is an exact maximal initial form of a singular
carrier, so its Hessian singularity should not be a separate caller
obligation.

The generic maximal-initial theorem supplies exactly this transport.  Thus a
Newton consumer now only has to provide:

* an exposing weight and maximal level;
* confinement of the exposed polynomial to one honest rank-three line; and
* nonzero coefficients at the two endpoints.

Everything from Hessian singularity through the autonomous polynomial terminal
certificate is automatic.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Exposed rank-three edge -> polynomial autonomous terminal.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_exposed_edge
    {P : MvPolynomial (Fin 4) K}
    {w : Fin 4 → ℤ} {level : ℤ}
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M)
    (hu1 : 0 < u1)
    (hbound : HC4.Polynomial.IsWeightLE w level P)
    (hzero : HC4.Polynomial.hessianDeterminant P = 0)
    (hsupp : HC4.Polynomial.IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M
      (HC4.Polynomial.initialForm w level P))
    (hstart :
      MvPolynomial.coeff
        (HC4.Polynomial.rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M 0)
        (HC4.Polynomial.initialForm w level P) ≠ 0)
    (hend :
      MvPolynomial.coeff
        (HC4.Polynomial.rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M M)
        (HC4.Polynomial.initialForm w level P) ≠ 0) :
    HasRankThreePolynomialTerminalCertificate
      (phi := HC4.Polynomial.rankThreeLineCoefficientPolynomial
        v2 v3 v4 u1 u2 u3 u4 M
        (HC4.Polynomial.initialForm w level P))
      (((M * v2 : ℕ) : K))
      (((M * v3 : ℕ) : K))
      (((M * v4 : ℕ) : K))
      (u1 : K)
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) := by
  have hdet :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm w level P) = 0 :=
    HC4.Polynomial.hessianDeterminant_initialForm_eq_zero_of_eq_zero
      w level P hbound hzero
  exact hasRankThreePolynomialTerminalCertificate_of_supported_edge
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet

end

end HC4.RationalRigidity
