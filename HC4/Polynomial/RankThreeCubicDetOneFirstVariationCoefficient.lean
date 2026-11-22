import HC4.Polynomial.RankThreeCubicDetOneFirstVariationProduct
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic

/-!
# Polynomial first-variation determinant coefficient (singular-safe)

Let A and B be square matrices over any commutative ring.
The coefficient of t in det(A + t B) equals the trace of
adj(A) B. We prove this using the Leibniz determinant expansion
and the verified one-linear-factor product formula, rather than
any inverse of A.

The theorem is the matrix-algebra side of the source weight-five
determinant calculation. No det(A) ≠ 0 assumption is present.
-/

namespace HC4.Polynomial

open _root_.Polynomial
open scoped Matrix BigOperators
noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A determinant product with column j replaced is the single
linear-factor contribution to that Leibniz permutation product. -/
theorem updateCol_perm_product_eq_single_linear_term
    (A B : Matrix ι ι R) (π : Equiv.Perm ι) (j : ι) :
    (∏ k : ι, (A.updateCol j (fun i => B i j)) (π k) k) =
      B (π j) j * ∏ k ∈ Finset.univ.erase j, A (π k) k := by
  classical
  have hrewrite :
      (∏ k : ι, (A.updateCol j (fun i => B i j)) (π k) k) =
        ∏ k : ι, if k = j then B (π k) j else A (π k) k := by
    apply Finset.prod_congr rfl
    intro k _
    simp [Matrix.updateCol_apply]
  rw [hrewrite]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun k : ι => if k = j then B (π k) j else A (π k) k)
    (Finset.mem_univ j)]
  simp only
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [hkj]

/-- The parameter-linear coefficient of the determinant is the
sum of its one-column replacements. This is valid even when the
unperturbed determinant is zero. -/
theorem coeff_one_det_C_add_X_C_eq_sum_updateCol
    (A B : Matrix ι ι R) :
    (Matrix.det (A.map Polynomial.C +
      (Polynomial.X : Polynomial R) • B.map Polynomial.C)).coeff 1 =
      ∑ j : ι, (A.updateCol j (fun i => B i j)).det := by
  classical
  let M : Matrix ι ι (Polynomial R) :=
    A.map Polynomial.C + (Polynomial.X : Polynomial R) • B.map Polynomial.C
  have hMentry (i j : ι) :
      M i j = Polynomial.C (A i j) +
        (Polynomial.X : Polynomial R) * Polynomial.C (B i j) := by
    rfl
  have hcoeff (π : Equiv.Perm ι) :
      ((Equiv.Perm.sign π) •
        (∏ k : ι, M (π k) k)).coeff 1 =
      (Equiv.Perm.sign π) •
        (∑ j : ι, B (π j) j *
          ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
    rw [_root_.Polynomial.coeff_smul]
    simp_rw [hMentry]
    rw [coeff_one_prod_C_add_X_C]
  change M.det.coeff 1 = _
  calc
    M.det.coeff 1 =
        ∑ π : Equiv.Perm ι,
          (Equiv.Perm.sign π) •
            (∑ j : ι, B (π j) j *
              ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
        rw [Matrix.det_apply, _root_.Polynomial.finset_sum_coeff]
        apply Finset.sum_congr rfl
        intro π _
        exact hcoeff π
    _ = ∑ j : ι,
          ∑ π : Equiv.Perm ι,
            (Equiv.Perm.sign π) •
              (B (π j) j *
                ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
          simp only [Finset.smul_sum]
          rw [Finset.sum_comm]
    _ = ∑ j : ι,
          (A.updateCol j (fun i => B i j)).det := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.det_apply]
          apply Finset.sum_congr rfl
          intro π _
          rw [updateCol_perm_product_eq_single_linear_term]

/-- The general singular-safe first variation, used for the
cubic Hessian whose determinant is identically zero. -/
theorem coeff_one_det_C_add_X_C_eq_adjugate_trace
    (A B : Matrix ι ι R) :
    (Matrix.det (A.map Polynomial.C +
      (Polynomial.X : Polynomial R) • B.map Polynomial.C)).coeff 1 =
      (A.adjugate * B).trace := by
  rw [coeff_one_det_C_add_X_C_eq_sum_updateCol]
  exact sum_det_updateCol_eq_adjugate_trace A B

end
end HC4.Polynomial
