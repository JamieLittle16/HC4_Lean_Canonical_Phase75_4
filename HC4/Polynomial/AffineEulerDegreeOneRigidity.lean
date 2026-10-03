import HC4.Polynomial.AffineEulerTwoRootRigidity
import HC4.Polynomial.RankThreeDegreeOnePencilRealisation
import Mathlib.Tactic

/-!
# Degree-one rigidity for the affine two-root Euler equation

The planar staircase classification gives coordinate-zero degree at most one
on every fixed pair-degree fibre.  This file records the tiny algebraic
consequence needed by A19: a nonzero degree-at-most-one solution of the affine
two-root equation with positive lower root `j` must have `j = 1`.

Moreover the solution is a nonzero scalar multiple of the affine factor
`c + d X`.  Thus the first interior fibre, if it exists, has pair degree two
and carries both adjacent source monomials in the locked coefficient ratio.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficient one of the affine two-root residual on a linear polynomial. -/
theorem coeff_one_affineTwoRootEulerOperator_linear
    (c d : K) (j : ℕ) (a0 a1 : K) :
    (affineTwoRootEulerOperator c d j
      (Polynomial.C a0 + Polynomial.C a1 * Polynomial.X)).coeff 1 =
      (j : K) * ((j : K) - 1) * d ^ 2 * a1 := by
  unfold affineTwoRootEulerOperator affineEulerLinear
  simp [Polynomial.derivative_add, Polynomial.derivative_mul]
  push_cast
  ring

/-- Constant coefficient of the same residual. -/
theorem coeff_zero_affineTwoRootEulerOperator_linear
    (c d : K) (j : ℕ) (a0 a1 : K) :
    (affineTwoRootEulerOperator c d j
      (Polynomial.C a0 + Polynomial.C a1 * Polynomial.X)).coeff 0 =
      (j : K) * ((j : K) + 1) * d ^ 2 * a0 -
        2 * (j : K) * d * c * a1 := by
  unfold affineTwoRootEulerOperator affineEulerLinear
  simp [Polynomial.derivative_add, Polynomial.derivative_mul]
  push_cast
  ring

/-- **Nonzero degree-one affine two-root solutions are primitive.**

If `j > 0`, `d != 0`, `phi != 0`, `deg phi <= 1`, and the affine two-root
operator vanishes, then `j=1`.  The polynomial is a nonzero scalar multiple
of the affine factor itself. -/
theorem affineTwoRoot_degreeOne_primitive
    (c d : K) (hc : c ≠ 0) (hd : d ≠ 0)
    (j : ℕ) (hj : 0 < j)
    (phi : Polynomial K) (hphi : phi ≠ 0)
    (hdeg : phi.natDegree ≤ 1)
    (hzero : affineTwoRootEulerOperator c d j phi = 0) :
    j = 1 ∧
      ∃ lam : K, lam ≠ 0 ∧
        phi = Polynomial.C lam * affineEulerLinear c d := by
  let a0 : K := phi.coeff 0
  let a1 : K := phi.coeff 1
  have hlin :
      phi = Polynomial.C a0 + Polynomial.C a1 * Polynomial.X := by
    dsimp [a0, a1]
    exact eq_C_add_C_mul_X_of_natDegree_le_one phi hdeg
  have h1raw := congrArg (fun p : Polynomial K => p.coeff 1) hzero
  have h0raw := congrArg (fun p : Polynomial K => p.coeff 0) hzero
  rw [hlin, coeff_one_affineTwoRootEulerOperator_linear] at h1raw
  rw [hlin, coeff_zero_affineTwoRootEulerOperator_linear] at h0raw
  simp only [Polynomial.coeff_zero] at h1raw h0raw

  have hjone : j = 1 := by
    by_contra hjne
    have hjtwo : 2 ≤ j := by omega
    have hjK : (j : K) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by omega)
    have hjm1K : (j : K) - 1 ≠ 0 := by
      intro hz
      have hcast : (j : K) = 1 := sub_eq_zero.mp hz
      have hnat : j = 1 := by exact_mod_cast hcast
      omega
    have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
    have hpref1 : (j : K) * ((j : K) - 1) * d ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hjK hjm1K) hd2
    have ha1 : a1 = 0 := by
      exact (mul_eq_zero.mp (by simpa [mul_assoc] using h1raw)).resolve_left hpref1
    rw [ha1, mul_zero, sub_zero] at h0raw
    have hjp1K : (j : K) + 1 ≠ 0 := by
      have hcast : (((j + 1 : ℕ) : K)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (by omega)
      simpa [Nat.cast_add] using hcast
    have hpref0 : (j : K) * ((j : K) + 1) * d ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hjK hjp1K) hd2
    have ha0 : a0 = 0 := by
      exact (mul_eq_zero.mp (by simpa [mul_assoc] using h0raw)).resolve_left hpref0
    apply hphi
    rw [hlin, ha0, ha1]
    simp

  subst j
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hrel : d * a0 = c * a1 := by
    norm_num at h0raw
    have hdK : d ≠ 0 := hd
    have htwo : (2 : K) ≠ 0 := by norm_num
    have hpref : 2 * d ≠ 0 := mul_ne_zero htwo hdK
    have hfac :
        (2 * d) * (d * a0 - c * a1) = 0 := by
      calc
        (2 * d) * (d * a0 - c * a1) =
          2 * d ^ 2 * a0 - 2 * d * c * a1 := by ring
        _ = 0 := h0raw
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hpref)
  have ha1 : a1 ≠ 0 := by
    intro ha1z
    rw [ha1z, mul_zero] at hrel
    have ha0 : a0 = 0 := by
      exact (mul_eq_zero.mp hrel).resolve_left hd
    apply hphi
    rw [hlin, ha0, ha1z]
    simp
  let lam : K := a1 / d
  have hlam : lam ≠ 0 := div_ne_zero ha1 hd
  refine ⟨rfl, lam, hlam, ?_⟩
  rw [hlin]
  unfold affineEulerLinear
  dsimp [lam]
  have hda0 : a0 = c * (a1 / d) := by
    field_simp [hd]
    simpa [mul_comm] using hrel
  rw [hda0]
  simp only [Polynomial.C_mul]
  field_simp [hd]
  ring

end

end HC4.Polynomial
