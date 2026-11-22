import HC4.Polynomial.RankThreeCubicSourceNormalQuadraticOrTriple
import Mathlib.Tactic

/-!
# Exact triple-factor normal form of the cubic Hessian determinant

A nonzero homogeneous cubic determinant factoring as p²*c, with
p,c both exactly degree one, has a genuinely triple linear factor
when p divides c. Its complementary quotient has degree zero,
hence is a nonzero scalar.

Thus the degeneracy alternative p|c is not a vague third factor:
  det H = C(lambda) * p³,    lambda != 0.

This is pure polynomial algebra and uses no source endpoint
hypotheses. It supplies the exact model for the triple branch.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- If a nonzero linear complementary factor is itself divisible
by the repeated linear factor, the cubic determinant is a
nonzero scalar multiple of that prime cubed. -/
theorem repeatedLinearCofactor_dvd_implies_exactTriple
    (D p c : B3 K)
    (hfactor : D = (p * p) * c)
    (hp0 : p ≠ 0)
    (hc0 : c ≠ 0)
    (hpdeg : p.totalDegree = 1)
    (hcdeg : c.totalDegree = 1)
    (hpc : p ∣ c) :
    ∃ lambda : K, lambda ≠ 0 ∧
      D = MvPolynomial.C lambda * (p * p * p) := by
  classical
  obtain ⟨u, hu⟩ := hpc
  have hu0 : u ≠ 0 := by
    intro hz
    exact hc0 (by rw [hu, hz, mul_zero])
  have hdegMul :
      c.totalDegree = p.totalDegree + u.totalDegree := by
    rw [hu]
    exact MvPolynomial.totalDegree_mul_of_isDomain hp0 hu0
  have huDegree : u.totalDegree = 0 := by omega
  have hconstant :
      u = MvPolynomial.C (u.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp huDegree
  let lambda : K := u.coeff 0
  have hlambda : lambda ≠ 0 := by
    intro hz
    apply hu0
    rw [hconstant]
    simp [lambda, hz]
  refine ⟨lambda, hlambda, ?_⟩
  rw [hfactor, hu, hconstant]
  ring

end
end HC4.Polynomial.RankThreeCubic
