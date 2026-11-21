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
        ∑ i : Fin 3, ((X i * pderiv i p) * q + p * (X i * pderiv i q)) := by
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
      rw [he, MvPolynomial.coeff_smul, nsmul_eq_mul]
      by_cases h : m = d
      · subst m
        simp [MvPolynomial.coeff_monomial]
      · simp [MvPolynomial.coeff_monomial, h, Ne.symm h]

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
  have hqe : transverseEuler q = (3 : B K) * q := by
    simpa [transverseEuler, nsmul_eq_mul] using hq.sum_X_mul_pderiv
  have hre : transverseEuler r = (4 : B K) * r := by
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
  calc
    p = ∑ i : Fin 3, X i * pderiv i p := he.symm
    _ = ∑ i : Fin 3, MvPolynomial.C (coeff 0 (pderiv i p)) * X i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hconst i]
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

private theorem transverseEuler_sum (v : Fin 3 → B K) :
    transverseEuler (∑ j, v j) = ∑ j, transverseEuler (v j) := by
  unfold transverseEuler
  simp_rw [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- An invertible homogeneous degree-one Hessian block has no
nonlinear polynomial kernel correction. If H W = r and r is quadratic,
then any polynomial solution W is linear. This avoids adjugate
expansion and is the exact source-side pole-free rigidity step. -/
theorem exists_linear_matrix_of_poleFree_hessianEquation
    (H : Matrix (Fin 3) (Fin 3) (B K))
    (r W : Fin 3 → B K)
    (hH : ∀ i j, (H i j).IsHomogeneous 1)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hdet : H.det ≠ 0)
    (heq : H *ᵥ W = r) :
    ∃ N : Matrix (Fin 3) (Fin 3) K,
      ∀ i, W i = ∑ j : Fin 3, MvPolynomial.C (N i j) * X j := by
  classical
  have hHE (i j : Fin 3) : transverseEuler (H i j) = H i j := by
    simpa [transverseEuler] using (hH i j).sum_X_mul_pderiv
  have hRE (i : Fin 3) : transverseEuler (r i) = (2 : B K) * r i := by
    simpa [transverseEuler, nsmul_eq_mul] using (hr i).sum_X_mul_pderiv
  have hi (i : Fin 3) : (∑ j : Fin 3, H i j * W j) = r i := by
    simpa only [Matrix.mulVec, dotProduct] using congrFun heq i
  have hE (i : Fin 3) :
      (∑ j : Fin 3, H i j * transverseEuler (W j)) = r i := by
    have h := congrArg transverseEuler (hi i)
    rw [transverseEuler_sum] at h
    simp_rw [transverseEuler_mul, hHE] at h
    rw [hRE i, Finset.sum_add_distrib, hi i] at h
    linear_combination h
  let U : Fin 3 → B K := fun j => transverseEuler (W j) - W j
  have hker : H *ᵥ U = 0 := by
    funext i
    change (∑ j : Fin 3, H i j * U j) = 0
    calc
      (∑ j : Fin 3, H i j * U j) =
          (∑ j : Fin 3, H i j * transverseEuler (W j)) -
          ∑ j : Fin 3, H i j * W j := by
            simp [U, mul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [hE i, hi i, sub_self]
  have hscalar : H.det • U = 0 := by
    rw [← Matrix.one_mulVec U, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul,
      ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  have hEuler (i : Fin 3) : transverseEuler (W i) = W i := by
    have hh := congrFun hscalar i
    change H.det * (transverseEuler (W i) - W i) = 0 at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hdet)
  let N : Matrix (Fin 3) (Fin 3) K :=
    fun i j => coeff 0 (pderiv j (W i))
  refine ⟨N, ?_⟩
  intro i
  exact linearForm_of_isHomogeneous_one (W i)
    (isHomogeneous_one_of_transverseEuler_eq_self (W i) (hEuler i))

/-- A fraction-field characteristic with no pole has a degree-one
polynomial representative and therefore a constant linear velocity,
provided its defining Hessian equation has the source's homogeneous
degrees. No rational denominator classification is assumed here:
the pole-free hypothesis is explicitly an embedded polynomial
representative for each velocity coordinate. -/
theorem exists_linear_matrix_of_poleFree_fractionKernel
    {F : Type*} [Field F] (g : B K →+* F) (hg : Function.Injective g)
    (H : Matrix (Fin 3) (Fin 3) (B K)) (r : Fin 3 → B K)
    (V : Fin 3 → F)
    (hH : ∀ i j, (H i j).IsHomogeneous 1)
    (hr : ∀ i, (r i).IsHomogeneous 2)
    (hdet : H.det ≠ 0)
    (hkernel : (H.map g) *ᵥ V = fun i => g (r i))
    (hpoleFree : ∀ i, ∃ p : B K, g p = V i) :
    ∃ N : Matrix (Fin 3) (Fin 3) K,
      ∀ i, V i = g (∑ j : Fin 3, MvPolynomial.C (N i j) * X j) := by
  classical
  choose W hW using hpoleFree
  have hpoly : H *ᵥ W = r := by
    funext i
    apply hg
    calc
      g ((H *ᵥ W) i) = ((H.map g) *ᵥ V) i := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hW]
      _ = g (r i) := congrFun hkernel i
  obtain ⟨N, hN⟩ :=
    exists_linear_matrix_of_poleFree_hessianEquation H r W hH hr hdet hpoly
  refine ⟨N, ?_⟩
  intro i
  rw [← hW i, hN i]

end
end HC4.Polynomial.RankThreeCubic
