import HC4.Polynomial.RankThreeCubicPoleSquarefreeResidue
import Mathlib

/-!
# Low-degree repeated factors in the cubic Hessian determinant

When a nonzero polynomial has total degree at most three, a
nonsquarefree factorisation has an irreducible repeated factor of
total degree exactly one.  This is a general UFD statement, not
a contradiction of the genuine cubic source.

The full-rank cubic transverse Hessian has a homogeneous cubic
determinant. Transporting this degree bound from the source is
the separate input to the final source-facing theorem.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- In three variables, a nonzero nonsquarefree polynomial of total
degree at most three has a repeated irreducible factor of degree one.
The factor can be affine linear here; its homogeneous linearity is
a separate consequence of homogeneous source data. -/
theorem exists_degree_one_repeated_irreducible_of_cubic_degree
    (D : B3 K)
    (hD : D ≠ 0)
    (hdeg : D.totalDegree ≤ 3)
    (hnot : ¬ Squarefree D) :
    ∃ p : B3 K, Irreducible p ∧ p * p ∣ D ∧ p.totalDegree = 1 := by
  classical
  have hbad : ∃ p : B3 K, Irreducible p ∧ p * p ∣ D := by
    by_contra h
    apply hnot
    apply (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hD).2
    intro p hp hpp
    exact h ⟨p, hp, hpp⟩
  obtain ⟨p, hp, hpp⟩ := hbad
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdegsq : (p * p).totalDegree = p.totalDegree + p.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hp0 hp0
  have hle : (p * p).totalDegree ≤ D.totalDegree :=
    MvPolynomial.totalDegree_le_of_dvd_of_isDomain hpp hD
  have hpos : 0 < p.totalDegree := by
    by_contra hn
    have hzero : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hn
    have hconst : p = C (p.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
    have hc0 : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp0
      rw [hconst, hc, map_zero]
    have hu : IsUnit p :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced).2
        ⟨isUnit_iff_ne_zero.mpr hc0, hzero⟩
    exact hp.not_isUnit hu
  have hpdeg : p.totalDegree = 1 := by omega
  exact ⟨p, hp, hpp, hpdeg⟩

/-- A nonsquarefree source transverse Hessian determinant with the
cubic total-degree bound has a repeated degree-one irreducible
factor. The nonzero Hessian determinant is already supplied by
the source-level characteristic construction. -/
theorem exists_sourceCubic_repeated_linear_factor_of_degree_bound
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hreg : (sourceTransverseHessian a L).det ≠ 0)
    (hdeg : (sourceTransverseHessian a L).det.totalDegree ≤ 3)
    (hnot : ¬ Squarefree (sourceTransverseHessian a L).det) :
    ∃ p : B3 K, Irreducible p ∧
      p * p ∣ (sourceTransverseHessian a L).det ∧
      p.totalDegree = 1 :=
  exists_degree_one_repeated_irreducible_of_cubic_degree
    (sourceTransverseHessian a L).det hreg hdeg hnot

end
end HC4.Polynomial.RankThreeCubic
