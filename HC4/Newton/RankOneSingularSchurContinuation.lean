import HC4.Newton.FirstSchurLayerLinearization
import Mathlib.Tactic

/-!
# Stationary-or-reflected continuation of an identically singular rank-one Schur series

After a binary Schur block has been aligned to a rank-one constant line, an
identically vanishing determinant leaves only two possibilities.

* The transverse entries never move again.  Then both the off-diagonal and
  kernel series vanish identically, so the projective kernel direction is
  fixed.
* There is a first positive transverse order `j`.  The first-order
  linearisation forces the kernel coefficient at `j` to vanish, hence the
  first transverse coefficient is genuinely off-diagonal.  Determinant
  singularity then forces the first kernel coefficient exactly at order
  `2*j`, with the square identity
      leading * C_(2*j) = B_j^2.

This is the finite algebraic continuation used by the source-honest reflected
staircase argument.  It introduces no clock, repair state, or geometric
hypothesis.
-/

namespace HC4.Newton

noncomputable section

universe u
variable {R : Type u} [CommRing R] [NoZeroDivisors R]

namespace RankOneSchurSeries

/-- **Stationary-or-reflected continuation.**

An identically singular rank-one Schur series with nonzero leading coefficient
either has a fixed transverse kernel forever, or has a first positive
off-diagonal order `j` and a forced nonzero kernel interaction at `2*j`.
-/
theorem stationary_or_reflectedInteraction
    (S : RankOneSchurSeries R)
    (hlead : S.leading ≠ 0)
    (hdet : S.determinant = 0) :
    (S.offDiag = 0 ∧ S.kernel = 0) ∨
      ∃ j : ℕ,
        0 < j ∧
        S.offDiag.coeff j ≠ 0 ∧
        (∀ n : ℕ, n < 2 * j → S.kernel.coeff n = 0) ∧
        S.leading * S.kernel.coeff (2 * j) =
          S.offDiag.coeff j * S.offDiag.coeff j ∧
        S.kernel.coeff (2 * j) ≠ 0 := by
  by_cases htrans : S.HasPositiveTransverseLayer
  · right
    let j := S.firstPositiveTransverseOrder htrans
    have hj : 0 < j := by
      simpa [j] using S.firstPositiveTransverseOrder_pos htrans
    have hoff :
        S.offDiag.coeff j ≠ 0 := by
      simpa [j] using
        S.firstTransverse_offDiag_ne_zero_of_determinant_eq_zero
          hlead hdet htrans
    have hkernelLower :
        ∀ n : ℕ, n < 2 * j → S.kernel.coeff n = 0 := by
      intro n hn
      exact S.kernel_coeff_eq_zero_before_twice_firstTransverse
        hlead hdet htrans n (by simpa [j] using hn)
    have hid :
        S.leading * S.kernel.coeff (2 * j) =
          S.offDiag.coeff j * S.offDiag.coeff j := by
      simpa [j] using
        S.kernel_coeff_twice_firstTransverse_identity
          hlead hdet htrans
    have hkernel :
        S.kernel.coeff (2 * j) ≠ 0 := by
      simpa [j] using
        S.kernel_coeff_twice_firstTransverse_ne_zero
          hlead hdet htrans
    exact ⟨j, hj, hoff, hkernelLower, hid, hkernel⟩
  · left
    exact ⟨
      S.offDiag_eq_zero_of_not_hasPositiveTransverseLayer htrans,
      S.kernel_eq_zero_of_not_hasPositiveTransverseLayer htrans⟩

end RankOneSchurSeries

end

end HC4.Newton
