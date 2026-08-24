import HC4.RationalRigidity.RankThreeSupportedEndpointBoundary
import Mathlib.Tactic

/-!
# A18.5.44: primitive balanced endpoint shape

A18.5.42 leaves an actual supported rank-three terminal with primitive
omitted-coordinate step `u1 = 1` and at least one vanishing transverse
coordinate.  The symmetric balance equation then has almost no freedom.

For a primitive endpoint

    u = (1,u2,u3,u4),
    a + b*u2 = b*u3 + a*u4,

with `a,b>0` and a transverse zero, exactly one of the following support
shapes occurs:

* `p`:              `(1,0,0,1)`;
* sparse `r`:       `(1,0,F,0)`, `F>0`;
* rank-three `sp`:  `(1,E,0,F)`, `E,F>0`;
* rank-three `rq`:  `(1,E,F,0)`, `E,F>0`.

This is deliberately a support-shape statement.  The arithmetic parameters
of the `r`/`s` generators can be recovered later from the existing facet
normal forms when the terminal pencil calculation needs them.
-/

namespace HC4.RationalRigidity

noncomputable section

open HC4.Polynomial
open HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Primitive balanced boundary endpoints have exactly the four shapes used
by the final rank-three dispatch. -/
theorem balanced_unit_transverseBoundary_shape
    {a b u2 u3 u4 : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hBal : Balanced a b ⟨1, u2, u3, u4⟩)
    (hzero : u2 = 0 ∨ u3 = 0 ∨ u4 = 0) :
    (u2 = 0 ∧ u3 = 0 ∧ u4 = 1) ∨
    (u2 = 0 ∧ 0 < u3 ∧ u4 = 0) ∨
    (0 < u2 ∧ u3 = 0 ∧ 0 < u4) ∨
    (0 < u2 ∧ 0 < u3 ∧ u4 = 0) := by
  change a * 1 + b * u2 = b * u3 + a * u4 at hBal
  simp only [mul_one] at hBal
  by_cases hu2 : u2 = 0
  · subst u2
    simp only [mul_zero, add_zero] at hBal
    by_cases hu3 : u3 = 0
    · subst u3
      simp only [mul_zero, zero_add] at hBal
      have hu4 : u4 = 1 := by
        have hEq : a * u4 = a * 1 := by simpa using hBal.symm
        exact Nat.mul_left_cancel ha hEq
      exact Or.inl ⟨rfl, rfl, hu4⟩
    · have hu3pos : 0 < u3 := Nat.pos_of_ne_zero hu3
      have hbu3 : 0 < b * u3 := Nat.mul_pos hb hu3pos
      have hu4 : u4 = 0 := by
        by_contra hu4ne
        have hu4pos : 0 < u4 := Nat.pos_of_ne_zero hu4ne
        have ha_le : a ≤ a * u4 := by
          have h1 : 1 ≤ u4 := hu4pos
          have := Nat.mul_le_mul_left a h1
          simpa using this
        omega
      exact Or.inr (Or.inl ⟨rfl, hu3pos, hu4⟩)
  · have hu2pos : 0 < u2 := Nat.pos_of_ne_zero hu2
    rcases hzero with hu2zero | hu3zero | hu4zero
    · exact (hu2 hu2zero).elim
    · subst u3
      have hu4 : 0 < u4 := by
        by_contra hu4not
        have hu4zero : u4 = 0 := Nat.eq_zero_of_not_pos hu4not
        subst u4
        simp only [mul_zero, add_zero] at hBal
        have habpos : 0 < a + b * u2 :=
          Nat.add_pos_left ha _
        omega
      exact Or.inr (Or.inr (Or.inl ⟨hu2pos, rfl, hu4⟩))
    · subst u4
      by_cases hu3 : u3 = 0
      · subst u3
        simp only [mul_zero, add_zero] at hBal
        have habpos : 0 < a + b * u2 :=
          Nat.add_pos_left ha _
        omega
      · exact Or.inr (Or.inr (Or.inr
          ⟨hu2pos, Nat.pos_of_ne_zero hu3, rfl⟩))

/-- **Actual supported terminal endpoint shape.**

The far endpoint of a singular balanced supported rank-three edge has, after
the primitive `u1=1` normalisation forced by the terminal ODE, exactly one of
the four finite support shapes above. -/
theorem supported_rankThree_edge_primitive_endpoint_shape
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hv2 : 0 < v2) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hM : 0 < M) (hu1 : 0 < u1)
    (hbalanced : HasBalancedMvSupport a b F)
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
    u1 = 1 ∧
      ((u2 = 0 ∧ u3 = 0 ∧ u4 = 1) ∨
       (u2 = 0 ∧ 0 < u3 ∧ u4 = 0) ∨
       (0 < u2 ∧ u3 = 0 ∧ 0 < u4) ∨
       (0 < u2 ∧ 0 < u3 ∧ u4 = 0)) := by
  have hendpoint := supported_rankThree_edge_endpoint_zero
    hv2 hv3 hv4 hM hu1 hsupp hstart hend hdet
  let eM := rankThreeLineExponentFinsupp
    v2 v3 v4 u1 u2 u3 u4 M M
  have heMmem : eM ∈ F.support :=
    MvPolynomial.mem_support_iff.mpr hend
  have hBalMv : IsBalancedExponent a b eM := hbalanced eM heMmem
  have hBalE : Balanced a b (toToricExponent eM) :=
    (isBalancedExponent_iff_balanced a b eM).1 hBalMv
  have hBalPrimitive : Balanced a b ⟨1, u2, u3, u4⟩ := by
    change
      a * (M * u1) + b * (M * u2) =
        b * (M * u3) + a * (M * u4) at hBalE
    rw [hendpoint.1] at hBalE
    have hfac :
        M * (a * 1 + b * u2) =
          M * (b * u3 + a * u4) := by
      calc
        M * (a * 1 + b * u2) =
            a * (M * 1) + b * (M * u2) := by ring
        _ = b * (M * u3) + a * (M * u4) := hBalE
        _ = M * (b * u3 + a * u4) := by ring
    have hcancel : a * 1 + b * u2 = b * u3 + a * u4 :=
      Nat.mul_left_cancel hM hfac
    exact hcancel
  exact ⟨hendpoint.1,
    balanced_unit_transverseBoundary_shape ha hb hBalPrimitive hendpoint.2⟩

end

end HC4.RationalRigidity
