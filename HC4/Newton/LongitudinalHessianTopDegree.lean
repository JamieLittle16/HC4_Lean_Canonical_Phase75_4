import HC4.Newton.GeneralFourBlockSchur
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Highest longitudinal degree, with arbitrary lower source terms

After multiplying the longitudinal Hessian row and column by `X`, all entries
of the Hessian of a degree-`N` source have degree at most `N`. The coefficient
at degree `4*N` is therefore the determinant of the matrix of top coefficients.
Every lower-degree term is excluded by the degree bound on the entire source;
there is no assumption about the order of its parameter layers.

For a leading coefficient with zero second derivatives involving the kernel
coordinate, the top determinant is a negative square times its own transverse
Hessian minor. No restriction on the degree of the transverse part is imposed.
For a leading coefficient `a = b*z*w + g + k*y`, the determinant of this top
matrix is `N^2*b^2*k^2`. Thus `k` vanishes when the determinant is `X^2`
and `b` is nonzero. Identifying an arbitrary terminal's leading coefficient
with this transverse form remains an additional mathematical obligation.
-/

namespace HC4.Newton
noncomputable section

variable {R : Type*} [CommRing R]

/-- Top determinant extraction under a common entry-degree bound. This is
the arbitrary-degree version of Mathlib's affine matrix coefficient lemma. -/
theorem matrix_det_top_coefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial R)) (N : ℕ)
    (hdegree : ∀ i j, (M i j).natDegree ≤ N) :
    M.det.coeff (Fintype.card ι * N) =
      Matrix.det (fun i j => (M i j).coeff N : Matrix ι ι R) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Finset.mem_univ, forall_true_left]
  intro g
  rw [Polynomial.coeff_smul]
  congr 1
  simpa using Polynomial.coeff_prod_of_natDegree_le
    (s := Finset.univ) (fun i => M (g i) i) N (fun i _ => hdegree (g i) i)

/-- Multiply just the longitudinal row and column by the polynomial variable.
This balances the two longitudinal derivative losses in a Hessian. -/
def longitudinalHessianDegreeScale (H : Matrix (Fin 4) (Fin 4) (Polynomial R)) :
    Matrix (Fin 4) (Fin 4) (Polynomial R) :=
  Matrix.diagonal ![Polynomial.X, 1, 1, 1] * H *
    Matrix.diagonal ![Polynomial.X, 1, 1, 1]

theorem longitudinalHessianDegreeScale_det
    (H : Matrix (Fin 4) (Fin 4) (Polynomial R)) :
    (longitudinalHessianDegreeScale H).det = Polynomial.X^2 * H.det := by
  simp [longitudinalHessianDegreeScale, Matrix.det_mul, Matrix.det_diagonal,
    Fin.prod_univ_four]
  ring

/-- Top matrix of `x^N*a(y,z,w)` when its second derivatives involving
`y` vanish. The transverse minor belongs to this same leading matrix. -/
def longitudinalHessianTopKernelBlock (n a k az aw zz zw ww : R) : GeneralFourBlock R where
  a := n*(n-1)*a
  b := n*k
  p := n*az
  q := n*aw
  d := 0
  r := 0
  s := 0
  x := zz
  y := zw
  z := ww

theorem longitudinalHessianTopKernelBlock_determinant
    (n a k az aw zz zw ww : R) :
    (longitudinalHessianTopKernelBlock n a k az aw zz zw ww).determinantCore =
      -(n^2*k^2)*(zz*ww-zw^2) := by
  simp [longitudinalHessianTopKernelBlock, GeneralFourBlock.determinantCore]
  ring

/-- Any positive longitudinal degree is allowed. The nonzero minor is on the
same leading coefficient matrix as the kernel entry being eliminated. -/
theorem longitudinalHessianTopKernelBlock_kernel_eq_zero
    [IsDomain R] [CharZero R]
    (M : Matrix (Fin 4) (Fin 4) (Polynomial R)) (N : ℕ) (hN : 0 < N)
    (a k az aw zz zw ww : R) (hminor : zz*ww-zw^2 ≠ 0)
    (hdegree : ∀ i j, (M i j).natDegree ≤ N)
    (htop : (fun i j => (M i j).coeff N : Matrix (Fin 4) (Fin 4) R) =
      (longitudinalHessianTopKernelBlock (N : R) a k az aw zz zw ww).matrix)
    (hdet : M.det = Polynomial.X^2) : k = 0 := by
  have htopdet := matrix_det_top_coefficient M N hdegree
  rw [htop, GeneralFourBlock.matrix_det,
    longitudinalHessianTopKernelBlock_determinant, hdet] at htopdet
  have hindex : 4*N ≠ 2 := by omega
  have hz : -((N : R)^2*k^2)*(zz*ww-zw^2) = 0 := by
    simpa [Polynomial.coeff_X_pow, hindex] using htopdet.symm
  have hn : (N : R) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hproduct : (N : R)^2*k^2 = 0 :=
    neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hminor)
  exact pow_eq_zero ((mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero 2 hn))

/-- Apply top-degree elimination to the original determinant-one matrix.
Only the entry-degree bounds and identification of the leading source jet
remain as hypotheses; determinant scaling is proved here. -/
theorem longitudinalHessianDegreeScale_kernel_eq_zero
    [IsDomain R] [CharZero R]
    (H : Matrix (Fin 4) (Fin 4) (Polynomial R)) (N : ℕ) (hN : 0 < N)
    (a k az aw zz zw ww : R) (hminor : zz*ww-zw^2 ≠ 0) (hdet : H.det = 1)
    (hdegree : ∀ i j, ((longitudinalHessianDegreeScale H) i j).natDegree ≤ N)
    (htop : (fun i j => ((longitudinalHessianDegreeScale H) i j).coeff N :
        Matrix (Fin 4) (Fin 4) R) =
      (longitudinalHessianTopKernelBlock (N : R) a k az aw zz zw ww).matrix) : k = 0 := by
  apply longitudinalHessianTopKernelBlock_kernel_eq_zero
    (longitudinalHessianDegreeScale H) N hN a k az aw zz zw ww hminor hdegree htop
  rw [longitudinalHessianDegreeScale_det, hdet, mul_one]

/-- The mixed quadratic coefficient is a specialization, not a degree-two
restriction on the longitudinal variable. -/
theorem longitudinalHessianTopKernelBlock_mixed_determinant
    (n a b k az aw : R) :
    (longitudinalHessianTopKernelBlock n a k az aw 0 b 0).determinantCore =
      n^2*b^2*k^2 := by
  rw [longitudinalHessianTopKernelBlock_determinant]
  ring

end
end HC4.Newton
