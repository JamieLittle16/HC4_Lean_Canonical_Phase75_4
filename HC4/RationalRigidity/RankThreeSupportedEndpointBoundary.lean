import HC4.RationalRigidity.RankThreeSupportedEdgeTerminal
import HC4.RationalRigidity.RankThreeAffineTopBoundary
import HC4.RationalRigidity.RankThreeUnitLongitudinalStep
import Mathlib.Tactic

/-!
# A18.5.42: the actual supported rank-three endpoint hits a transverse facet

For the finite honest line used by the Newton endgame the supported exponents
are

    e_j = (j*u1,
           (M-j)*v2 + j*u2,
           (M-j)*v3 + j*u3,
           (M-j)*v4 + j*u4).

The two endpoint coefficients are nonzero, so the extracted coefficient
polynomial has degree exactly `M`.  Repackage this finite line in the general
affine interface of A18.5.24.  The terminal ODE then gives `u1=1`, while the
A18.5.36 top-boundary theorem says `e_M` omits a coordinate.  Its zeroth
coordinate is the positive number `M`, so one of `u2,u3,u4` must vanish.

This is the exact finite endpoint split used by the terminal pencil cases; no
field-valued direction is left in the conclusion.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Actual supported endpoint boundary theorem.**

A singular genuine rank-three Newton edge with both endpoints present has
primitive omitted-coordinate step and its opposite endpoint lies on one of the
three transverse coordinate facets. -/
theorem supported_rankThree_edge_endpoint_zero
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
    u1 = 1 ∧ (u2 = 0 ∨ u3 = 0 ∨ u4 = 0) := by
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
  have hA : 0 < M * v2 := Nat.mul_pos hM hv2
  have hB : 0 < M * v3 := Nat.mul_pos hM hv3
  have hC : 0 < M * v4 := Nat.mul_pos hM hv4

  let L : RankThreeAffineLineData
      (M * v2) (M * v3) (M * v4) u1
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) phi := {
    exponent := fun j =>
      rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M j
    affine := by
      intro j hj
      have hjDeg : j ≤ phi.natDegree :=
        Polynomial.le_natDegree_of_mem_supp j hj
      have hjM : j ≤ M := by simpa [hdeg] using hjDeg
      have hline := rankThreeLineExponentFinsupp_cast_eq_affine
        (K := K) v2 v3 v4 u1 u2 u3 u4 M j hjM
      simpa [rankThreeIntegralLineBaseExponent,
        rankThreeIntegralLineDirection] using hline
  }

  have hcert := hasRankThreePolynomialTerminalCertificate_of_supported_edge
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  have hstep := rankThree_unit_longitudinal_step_of_certificate
    hA hB hC hu1 hphiDeg hphi0 hcert
  have hboundary := rankThreeAffineLine_topExponent_on_boundary_of_certificate
    L hA hB hC hu1 hphiDeg hphi0 hcert
  rw [hdeg] at hboundary
  rw [mvExponentOnBoundary_iff_coordinate_zero] at hboundary
  change
    rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M 0 = 0 ∨
    rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M 1 = 0 ∨
    rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M 2 = 0 ∨
    rankThreeLineExponentFinsupp v2 v3 v4 u1 u2 u3 u4 M M 3 = 0 at hboundary
  simp only [rankThreeLineExponentFinsupp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Nat.sub_self, zero_mul, zero_add] at hboundary

  have hMu1 : M * u1 ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hM) (Nat.ne_of_gt hu1)
  rcases hboundary with h0 | h2 | h3 | h4
  · exact (hMu1 h0).elim
  · have hu2 : u2 = 0 := (Nat.mul_eq_zero.mp h2).resolve_left (Nat.ne_of_gt hM)
    exact ⟨hstep.1, Or.inl hu2⟩
  · have hu3 : u3 = 0 := (Nat.mul_eq_zero.mp h3).resolve_left (Nat.ne_of_gt hM)
    exact ⟨hstep.1, Or.inr (Or.inl hu3)⟩
  · have hu4 : u4 = 0 := (Nat.mul_eq_zero.mp h4).resolve_left (Nat.ne_of_gt hM)
    exact ⟨hstep.1, Or.inr (Or.inr hu4)⟩

end

end HC4.RationalRigidity
