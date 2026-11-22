import HC4.Polynomial.RankThreeCubicDetOneWeightFiveProduct
import HC4.Polynomial.DeterminantWeight

/-!
# Weight-one gap in a determinant Leibniz expansion

This is a pure matrix-polynomial result, independent of the cubic
characteristic. If two square polynomial matrices have the same
entrywise upper weighted bounds and their entrywise differences are
strictly below the upper bounds MINUS ONE, then the determinant
components one weight below the nominal maximum coincide.

Every determinant permutation term has one common prescribed upper
weight. The proof uses only the verified finite-product gap lemma;
no 4x4 determinant is expanded.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {σ K ι : Type*}
variable [CommRing K] [DecidableEq σ]
variable [Fintype ι] [DecidableEq ι]

/-- A correction which is at least two weights below the nominal
leading matrix entries makes no contribution to the determinant's
first lower weighted component. -/
theorem initialForm_det_eq_of_entry_gapOne
    (w : σ → ℤ) (d : ℤ) (b : ι → ι → ℤ)
    (M N : Matrix ι ι (MvPolynomial σ K))
    (hweight : ∀ π : Equiv.Perm ι, (∑ i : ι, b (π i) i) = d)
    (hM : ∀ i j : ι, IsWeightLE w (b i j) (M i j))
    (hN : ∀ i j : ι, IsWeightLE w (b i j) (N i j))
    (hdiff : ∀ i j : ι, IsWeightLT w (b i j - 1)
      (M i j - N i j)) :
    initialForm w (d - 1) M.det =
      initialForm w (d - 1) N.det := by
  classical
  have hprod (π : Equiv.Perm ι) :
      initialForm w (d - 1) (∏ i : ι, M (π i) i) =
        initialForm w (d - 1) (∏ i : ι, N (π i) i) := by
    have hgap := prod_sub_prod_isWeightLT_gapOne
      (Finset.univ : Finset ι) w (fun i : ι => b (π i) i)
      (fun i : ι => M (π i) i) (fun i : ι => N (π i) i)
      (fun i _ => hM (π i) i)
      (fun i _ => hN (π i) i)
      (fun i _ => hdiff (π i) i)
    rw [hweight π] at hgap
    have hz := initialForm_eq_zero_of_isWeightLT hgap (le_refl (d - 1))
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  rw [Matrix.det_apply', Matrix.det_apply', map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro π _
  let c : K := ↑↑(Equiv.Perm.sign π)
  change initialForm w (d - 1)
      (MvPolynomial.C c * ∏ i : ι, M (π i) i) =
    initialForm w (d - 1)
      (MvPolynomial.C c * ∏ i : ι, N (π i) i)
  simp only [MvPolynomial.C_mul', initialForm_smul, hprod π]

end
end HC4.Polynomial
