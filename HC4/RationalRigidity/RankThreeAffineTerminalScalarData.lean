import HC4.RationalRigidity.RankThreeAffineTwoFixedEqualitiesImpossible

/-!
# A18.5.73a.4: compact nondependent affine terminal scalar data

The Newton first-contact presentation is large, but the final two-fixed
RationalRigidity contradiction only needs a small scalar terminal package.
The crucial elaboration choice is that all parameters of the terminal
certificate are *parameters of the structure*, not fields of the structure.
Thus the certificate field does not depend on record projections and its
projections stay cheap for the elaborator.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Presentation-free scalar data consumed by the two-fixed affine terminal
contradiction.  Every parameter occurring in the certificate is external to
this record, so no dependent projection is required downstream. -/
structure RankThreeAffineTerminalScalarData
    (A B C P : ℕ) (Q R S : K) (phi : Polynomial K) : Prop where
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  P_pos : 0 < P
  phi_degree_pos : 0 < phi.natDegree
  phi_coeff_zero_ne : phi.coeff 0 ≠ 0
  certificate : HasRankThreePolynomialTerminalCertificate
    (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S

/-- Two fixed transverse slopes eliminate the compact scalar terminal as soon
as the remaining slope is neither zero nor `-1`. -/
theorem RankThreeAffineTerminalScalarData.impossible_of_two_fixed
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (data : RankThreeAffineTerminalScalarData A B C P Q R S phi)
    (hR : R = 0)
    (hS : S = 0)
    (hQ : Q ≠ 0)
    (hQone : Q + 1 ≠ 0) : False := by
  exact rankThree_terminal_two_fixed_impossible_of_eq
    data.A_pos data.B_pos data.C_pos data.P_pos
    data.phi_degree_pos data.phi_coeff_zero_ne data.certificate
    hR hS hQ hQone

end

end HC4.RationalRigidity
