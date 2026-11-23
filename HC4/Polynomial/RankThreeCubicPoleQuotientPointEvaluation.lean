import HC4.Polynomial.RankThreeCubicDetOneFixedKernelPoleFullProfile
import Mathlib.Tactic

/-!
# Descend a source pole-quotient equation to any point on its plane

For q : K[y] → K[y]/(p), a polynomial equation q(f)=0
implies f(z)=0 at EVERY K-point z with p(z)=0, not merely
at the transverse origin. More generally, an equality q(f)=q(g)
specializes to f(z)=g(z) at such a point.

This small bridge allows a fixed pole-quotient kernel and its
constant longitudinal response to be evaluated at y=0, z, -z.
The full source Hessian evaluation theorem is a subsequent step.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K

theorem poleQuotient_zero_implies_pointEval_zero
    (p f : B3 K) (z : Fin 3 → K)
    (hpz : MvPolynomial.aeval z p = 0)
    (hf : Ideal.Quotient.mk (Ideal.span {p}) f = 0) :
    MvPolynomial.aeval z f = 0 := by
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hf
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  rw [hg, map_mul, hpz, zero_mul]

theorem poleQuotient_eq_implies_pointEval_eq
    (p f g : B3 K) (z : Fin 3 → K)
    (hpz : MvPolynomial.aeval z p = 0)
    (hf :
      Ideal.Quotient.mk (Ideal.span {p}) f =
        Ideal.Quotient.mk (Ideal.span {p}) g) :
    MvPolynomial.aeval z f = MvPolynomial.aeval z g := by
  have hzero :
      Ideal.Quotient.mk (Ideal.span {p}) (f - g) = 0 := by
    rw [map_sub, hf, sub_self]
  have hz :=
    poleQuotient_zero_implies_pointEval_zero p (f - g) z hpz hzero
  simpa only [map_sub, sub_eq_zero] using hz

end
end HC4.Polynomial.RankThreeCubic
