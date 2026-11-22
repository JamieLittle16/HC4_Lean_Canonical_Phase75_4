import HC4.Polynomial.RankThreeCubicDetOneFixedTangentUnitRepairOrTriple
import Mathlib.Tactic

/-!
# Units in a pole quotient cannot vanish at an origin on the pole

Let p belong to the kernel of evaluation at the transverse
origin in K[y_0,y_1,y_2]. Origin evaluation therefore factors
through K[y]/(p).

If the class of f in this quotient is a unit, its origin value
is a unit of K, hence nonzero. This works for ANY p vanishing at
the origin, without irreducibility or a degree assumption.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

/-- An invertible residue on a hyperplane through the origin has
a nonzero constant term before quotienting. -/
theorem poleQuotient_unit_implies_originEval_ne_zero
    (p f : B3 K)
    (hp0 : MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) p = 0)
    (hf : IsUnit
      (Ideal.Quotient.mk (Ideal.span {p}) f)) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) f ≠ 0 := by
  classical
  let ev : B3 K →+* K :=
    (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom
  have hevP : ev p = 0 := hp0
  have hkill : ∀ x : B3 K, x ∈ Ideal.span {p} → ev x = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx
    rw [ha, map_mul, hevP, zero_mul]
  let evQ : (B3 K ⧸ Ideal.span {p}) →+* K :=
    Ideal.Quotient.lift (Ideal.span {p}) ev hkill
  have hfunit : IsUnit (ev f) := by
    have ht := hf.map evQ
    simpa only [Ideal.Quotient.lift_mk] using ht
  exact isUnit_iff_ne_zero.mp hfunit

/-- The origin lies on a linear homogeneous pole hyperplane,
written in the explicit source normal-coefficient form. -/
theorem linearPole_originEval_eq_zero
    (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
       (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i)) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) p = 0 := by
  rw [hlin, map_sum]
  simp

/-- Combine the explicit linear equation with the quotient unit
condition, avoiding an extra origin-vanishing hypothesis. -/
theorem linearPoleQuotient_unit_implies_originEval_ne_zero
    (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
       (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (f : B3 K)
    (hf : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) f)) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) f ≠ 0 :=
  poleQuotient_unit_implies_originEval_ne_zero p f
    (linearPole_originEval_eq_zero p ell hlin) hf

end
end HC4.Polynomial.RankThreeCubic
