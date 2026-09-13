import HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
import Mathlib.Tactic

/-!
# A18.5.41: a genuine rank-three terminal crosses to a transverse facet

The initial affine exponent is `(0,A,B,C)` with `A,B,C>0`.  A18.5.39 gives
primitive omitted-coordinate step one and A18.5.36 gives boundary membership
of the far supported exponent.  Since the far coefficient index is the
positive degree `D`, its zeroth exponent is exactly `D`, hence is positive.
The boundary coordinate at the far end must therefore be one of the three
transverse coordinates.

This is the finite facet-transition statement needed before the two terminal
rank-three pencil normal forms are selected.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Far endpoint transverse-facet theorem.** -/
theorem rankThreeTerminal_top_transverse_coordinate_zero
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hu1 : 0 < u1)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    L.exponent phi.natDegree (0 : Fin 4) = phi.natDegree ∧
      (L.exponent phi.natDegree (1 : Fin 4) = 0 ∨
       L.exponent phi.natDegree (2 : Fin 4) = 0 ∨
       L.exponent phi.natDegree (3 : Fin 4) = 0) := by
  let N := rankThreeTerminal_binomialNormalForm
    L hA hB hC hu1 hphiDeg hphi0 hdet
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphi0
  have hDmem : phi.natDegree ∈ phi.support := by
    rw [Polynomial.mem_support_iff]
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  have hzero := L.exponent_zero_eq hDmem
  have hzeroD :
      L.exponent phi.natDegree (0 : Fin 4) = phi.natDegree := by
    simpa [N.omitted_step_eq_one] using hzero
  have hboundary := N.top_exponent_on_boundary
  rw [mvExponentOnBoundary_iff_coordinate_zero] at hboundary
  rcases hboundary with h0 | h1 | h2 | h3
  · rw [hzeroD] at h0
    omega
  · exact ⟨hzeroD, Or.inl h1⟩
  · exact ⟨hzeroD, Or.inr (Or.inl h2)⟩
  · exact ⟨hzeroD, Or.inr (Or.inr h3)⟩

end

end HC4.RationalRigidity
