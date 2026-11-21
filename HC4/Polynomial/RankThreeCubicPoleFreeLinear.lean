import HC4.Polynomial.RankThreeCubicLinearSquareAssembly
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Tactic

/-!
# A pole-free homogeneous rational cubic characteristic is linear

The adjugate formula for a full-rank transverse cubic Hessian gives
a degree-four numerator divided by a nonzero degree-three denominator.
If the rational velocity has no denominator pole (is represented by
ordinary transverse polynomials), its polynomial representative must
have degree one, hence equal a constant matrix times the variables.

This module isolates the polynomial degree argument, independent of
localization and Jordan normal forms.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial Finsupp
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- The Euler derivation in the three transverse variables. -/
def transverseEuler (p : B K) : B K :=
  ∑ i : Fin 3, X i * pderiv i p

private theorem transverseEuler_add (p q : B K) :
    transverseEuler (p + q) = transverseEuler p + transverseEuler q := by
  simp [transverseEuler, map_add, mul_add, Finset.sum_add_distrib]

private theorem transverseEuler_mul (p q : B K) :
    transverseEuler (p * q) =
      transverseEuler p * q + p * transverseEuler q := by
  unfold transverseEuler
  calc
    (∑ i : Fin 3, X i * pderiv i (p * q)) =
        ∑ i : Fin 3, (X i * pderiv i p) * q + p * (X i * pderiv i q) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [Derivation.leibniz, smul_eq_mul]
          ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

private theorem coeff_transverseEuler (p : B K) (m : Fin 3 →₀ ℕ) :
    coeff m (transverseEuler p) = (m.degree : K) * coeff m p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      rw [transverseEuler_add, coeff_add, hp, hq, coeff_add]
      ring
  | monomial d a =>
      have hh : (MvPolynomial.monomial d a : B K).IsHomogeneous d.degree :=
        MvPolynomial.isHomogeneous_monomial a rfl
      have he := hh.sum_X_mul_pderiv
      change transverseEuler (MvPolynomial.monomial d a : B K) =
        d.degree • MvPolynomial.monomial d a at he
      rw [he]
      by_cases h : m = d
      · subst m
        simp [MvPolynomial.coeff_monomial, nsmul_eq_mul]
      · simp [MvPolynomial.coeff_monomial, h, nsmul_eq_mul]

/-- Conversely to Euler's homogeneous identity, Euler(f)=f makes
a polynomial homogeneous of degree one in characteristic zero. -/
theorem isHomogeneous_one_of_transverseEuler_eq_self
    (p : B K) (hp : transverseEuler p = p) :
    p.IsHomogeneous 1 := by
  intro m hm
  have hc := coeff_transverseEuler p m
  rw [hp] at hc
  have hz : ((m.degree : K) - 1) * coeff m p = 0 := by
    linear_combination -hc
  have hdeg : (m.degree : K) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hm)
  have hn : m.degree = 1 := by exact_mod_cast hdeg
  simpa only [Finsupp.degree_eq_weight_one] using hn

/-- If q and r are homogeneous of degrees 3 and 4 and q ≠ 0,
any polynomial quotient r/q must be homogeneous of degree one. -/
theorem isHomogeneous_one_of_cubic_quartic_division
    (q p r : B K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 4)
    (hqne : q ≠ 0) (hprod : q * p = r) :
    p.IsHomogeneous 1 := by
  have hqe : transverseEuler q = (3 : K) * q := by
    simpa [transverseEuler, nsmul_eq_mul] using hq.sum_X_mul_pderiv
  have hre : transverseEuler r = (4 : K) * r := by
    simpa [transverseEuler, nsmul_eq_mul] using hr.sum_X_mul_pderiv
  have hE := congrArg transverseEuler hprod
  rw [transverseEuler_mul, hqe, hre, ← hprod] at hE
  have hp : q * (transverseEuler p - p) = 0 := by
    linear_combination hE
  have he : transverseEuler p = p :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hqne)
  exact isHomogeneous_one_of_transverseEuler_eq_self p he

/-- Homogeneous linear polynomials are exactly linear forms with
constant coefficients, extracted as derivatives at the origin. -/
theorem linearForm_of_isHomogeneous_one
    (p : B K) (hp : p.IsHomogeneous 1) :
    p = ∑ i : Fin 3, MvPolynomial.C (coeff 0 (pderiv i p)) * X i := by
  have hd (i : Fin 3) : (pderiv i p).IsHomogeneous 0 := by
    simpa using (hp.pderiv (i := i))
  have hconst (i : Fin 3) :
      pderiv i p = MvPolynomial.C (coeff 0 (pderiv i p)) :=
    totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr (hd i))
  have he := hp.sum_X_mul_pderiv
  simp only [one_smul] at he
  rw [← he]
  simp_rw [hconst]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pole-free cubic Cramer data is a constant-matrix linear velocity.

Here q is the nonzero cubic transverse Hessian determinant, r_i is the
quartic adjugate numerator and W_i is its polynomial quotient. -/
theorem exists_linear_matrix_of_poleFree_cubicCramer
    (q : B K) (r W : Fin 3 → B K)
    (hq : q.IsHomogeneous 3)
    (hqn : q ≠ 0)
    (hr : ∀ i, (r i).IsHomogeneous 4)
    (hdiv : ∀ i, q * W i = r i) :
    ∃ N : Matrix (Fin 3) (Fin 3) K,
      ∀ i, W i = ∑ j : Fin 3, MvPolynomial.C (N i j) * X j := by
  let N : Matrix (Fin 3) (Fin 3) K :=
    fun i j => coeff 0 (pderiv j (W i))
  refine ⟨N, ?_⟩
  intro i
  exact linearForm_of_isHomogeneous_one (W i)
    (isHomogeneous_one_of_cubic_quartic_division q (W i) (r i)
      hq (hr i) hqn (hdiv i))

end
end HC4.Polynomial.RankThreeCubic
