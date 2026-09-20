import HC4.Newton.FirstSchurLayerLinearization
import Mathlib.Tactic

/-!
# Off-diagonal gap forced by singularity and diagonal gaps

For a determinant-zero binary polynomial Schur series, if both diagonal
entries vanish below an order `q`, then the off-diagonal entry must vanish
below `q` as well.  Otherwise its first nonzero coefficient would contribute
a nonzero square to the determinant before either diagonal can contribute.

This is a state-free convolution lemma.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R] [NoZeroDivisors R]

namespace BinarySchurPolynomialSeries

/-- Diagonal coefficient gaps plus exact determinant zero force the same gap
on the off-diagonal entry. -/
theorem offDiag_coeff_eq_zero_below_of_diagonal_gap
    (S : BinarySchurPolynomialSeries R)
    (q : ℕ)
    (hactive : ∀ n : ℕ, n < q → S.active.coeff n = 0)
    (hkernel : ∀ n : ℕ, n < q → S.kernel.coeff n = 0)
    (hdet : S.determinant = 0) :
    ∀ n : ℕ, n < q → S.offDiag.coeff n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hdiagProduct :
          (S.active * S.kernel).coeff (2 * n) = 0 := by
        exact coeff_mul_eq_zero_before_twice_of_lower_zero
          S.active S.kernel
          (by omega)
          hactive hkernel
      have hoffLower :
          ∀ r : ℕ, r < n → S.offDiag.coeff r = 0 := by
        intro r hr
        exact ih r hr (lt_trans hr hn)
      have hoffSquare :
          (S.offDiag * S.offDiag).coeff (2 * n) =
            S.offDiag.coeff n * S.offDiag.coeff n := by
        exact coeff_mul_twice_eq_leading_mul_of_lower_zero
          S.offDiag S.offDiag hoffLower hoffLower
      have hcoeff : S.determinant.coeff (2 * n) = 0 := by
        rw [hdet]
        rfl
      unfold BinarySchurPolynomialSeries.determinant at hcoeff
      rw [Polynomial.coeff_sub, hdiagProduct, hoffSquare] at hcoeff
      have hsq :
          S.offDiag.coeff n * S.offDiag.coeff n = 0 := by
        simpa only [zero_sub, neg_eq_zero] using hcoeff
      rcases mul_eq_zero.mp hsq with hz | hz
      · exact hz
      · exact hz

end BinarySchurPolynomialSeries

end

end HC4.Newton
