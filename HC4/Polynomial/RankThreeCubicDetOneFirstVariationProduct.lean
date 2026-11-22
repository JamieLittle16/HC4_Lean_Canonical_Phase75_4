import HC4.Polynomial.RankThreeCubicDetOneFirstVariationColumns
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# First parameter coefficient of a product of linear polynomials

This is the coefficient-level counterpart of the determinant's
multilinearity. One obtains the degree-one coefficient by choosing
exactly one linear term, with all other factors constant.

The proof uses the polynomial derivative/product rule and hence
works over an arbitrary commutative ring (without divisions).
-/

namespace HC4.Polynomial

-- Use the global polynomial namespace, not HC4.Polynomial itself.
open _root_.Polynomial
open scoped BigOperators
noncomputable section

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- The degree-one coefficient of a polynomial is the constant
coefficient of its derivative, over any commutative ring. -/
theorem coeff_one_eq_derivative_eval_zero
    (P : Polynomial R) :
    P.coeff 1 = P.derivative.eval 0 := by
  rw [← _root_.Polynomial.coeff_zero_eq_eval_zero,
    _root_.Polynomial.coeff_derivative]
  simp

/-- The degree-one coefficient of a product of affine polynomials
comes from exactly one linear factor. -/
theorem coeff_one_prod_C_add_X_C
    (s : Finset ι) (a b : ι → R) :
    (∏ i ∈ s, (Polynomial.C (a i) +
        Polynomial.X * Polynomial.C (b i))).coeff 1 =
      ∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j := by
  let f : ι → Polynomial R :=
    fun i => Polynomial.C (a i) +
      Polynomial.X * Polynomial.C (b i)
  have hev (i : ι) : (f i).eval 0 = a i := by
    simp [f]
  have hdev (i : ι) : (f i).derivative.eval 0 = b i := by
    simp [f, _root_.Polynomial.derivative_add,
      _root_.Polynomial.derivative_mul]
  have hprod :
      derivative (∏ i ∈ s, f i) =
        ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * derivative (f i) := by
    simpa only [] using
      (_root_.Polynomial.derivative_prod
        (s := s.val) (f := f))
  change (∏ i ∈ s, f i).coeff 1 = _
  rw [coeff_one_eq_derivative_eval_zero, hprod,
    _root_.Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_prod,
    hdev]
  simp_rw [hev]
  ring

end
end HC4.Polynomial
