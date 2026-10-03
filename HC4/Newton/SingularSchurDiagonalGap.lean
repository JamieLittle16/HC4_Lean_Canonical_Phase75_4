import HC4.Newton.FirstSchurLayerLinearization
import HC4.Newton.RankOneSchurSeriesAlignment
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
        exact RankOneSchurSeries.coeff_mul_eq_zero_before_twice_of_lower_zero
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
        exact RankOneSchurSeries.coeff_mul_twice_eq_leading_mul_of_lower_zero
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

namespace GeneralFourBlock

/-- If one complementary source direction is absent below order `j`, and
the opposite complementary column vanishes on the special fibre, then the
`j`th cleared Schur off-diagonal coefficient is just the active constant
minor times the literal mixed Hessian coefficient.  This is the orientation
where `p,r,y` are the missing-row entries. -/
theorem schurB_coeff_eq_activeDet_zero_mul_y_of_left_gap
    (H : GeneralFourBlock (Polynomial R))
    {j : ℕ}
    (hp : ∀ n : ℕ, n < j → H.p.coeff n = 0)
    (hr : ∀ n : ℕ, n < j → H.r.coeff n = 0)
    (hy : ∀ n : ℕ, n < j → H.y.coeff n = 0)
    (hq0 : H.q.coeff 0 = 0)
    (hs0 : H.s.coeff 0 = 0) :
    H.schurB.coeff j =
      H.activeDet.coeff 0 * H.y.coeff j := by
  have htriple :
      ∀ (A M B : Polynomial R),
        (∀ n : ℕ, n < j → M.coeff n = 0) →
        B.coeff 0 = 0 →
        (A * M * B).coeff j = 0 := by
    intro A M B hM hB0
    have hAM : ∀ n : ℕ, n < j → (A * M).coeff n = 0 := by
      intro n hn
      rw [coeff_mul_eq_constant_mul_of_right_vanishes_below A M]
      · rw [hM n hn]
        simp
      · intro m hm
        exact hM m (lt_trans hm hn)
    rw [show A * M * B = B * (A * M) by ring]
    rw [coeff_mul_eq_constant_mul_of_right_vanishes_below B (A * M) hAM]
    rw [hB0]
    simp
  have hdpq : (H.d * H.p * H.q).coeff j = 0 :=
    htriple H.d H.p H.q hp hq0
  have hbps : (H.b * H.p * H.s).coeff j = 0 :=
    htriple H.b H.p H.s hp hs0
  have hbqr : (H.b * H.q * H.r).coeff j = 0 := by
    rw [show H.b * H.q * H.r = H.b * H.r * H.q by ring]
    exact htriple H.b H.r H.q hr hq0
  have hars : (H.a * H.r * H.s).coeff j = 0 :=
    htriple H.a H.r H.s hr hs0
  have hmain :
      (H.activeDet * H.y).coeff j =
        H.activeDet.coeff 0 * H.y.coeff j :=
    coeff_mul_eq_constant_mul_of_right_vanishes_below
      H.activeDet H.y hy
  unfold schurB
  rw [Polynomial.coeff_sub, hmain]
  have hcorr :
      (H.d * H.p * H.q -
          H.b * (H.p * H.s + H.q * H.r) +
          H.a * H.r * H.s).coeff j = 0 := by
    rw [show
      H.d * H.p * H.q -
            H.b * (H.p * H.s + H.q * H.r) +
            H.a * H.r * H.s =
        H.d * H.p * H.q - H.b * H.p * H.s -
          H.b * H.q * H.r + H.a * H.r * H.s by ring]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
    rw [hdpq, hbps, hbqr, hars]
    ring
  rw [hcorr]
  simp

/-- Right-oriented mirror of
`schurB_coeff_eq_activeDet_zero_mul_y_of_left_gap`: now `q,s,y` are the
missing-row entries and `p,r` vanish on the special fibre. -/
theorem schurB_coeff_eq_activeDet_zero_mul_y_of_right_gap
    (H : GeneralFourBlock (Polynomial R))
    {j : ℕ}
    (hq : ∀ n : ℕ, n < j → H.q.coeff n = 0)
    (hs : ∀ n : ℕ, n < j → H.s.coeff n = 0)
    (hy : ∀ n : ℕ, n < j → H.y.coeff n = 0)
    (hp0 : H.p.coeff 0 = 0)
    (hr0 : H.r.coeff 0 = 0) :
    H.schurB.coeff j =
      H.activeDet.coeff 0 * H.y.coeff j := by
  have htriple :
      ∀ (A M B : Polynomial R),
        (∀ n : ℕ, n < j → M.coeff n = 0) →
        B.coeff 0 = 0 →
        (A * M * B).coeff j = 0 := by
    intro A M B hM hB0
    have hAM : ∀ n : ℕ, n < j → (A * M).coeff n = 0 := by
      intro n hn
      rw [coeff_mul_eq_constant_mul_of_right_vanishes_below A M]
      · rw [hM n hn]
        simp
      · intro m hm
        exact hM m (lt_trans hm hn)
    rw [show A * M * B = B * (A * M) by ring]
    rw [coeff_mul_eq_constant_mul_of_right_vanishes_below B (A * M) hAM]
    rw [hB0]
    simp
  have hdpq : (H.d * H.p * H.q).coeff j = 0 := by
    rw [show H.d * H.p * H.q = H.d * H.q * H.p by ring]
    exact htriple H.d H.q H.p hq hp0
  have hbps : (H.b * H.p * H.s).coeff j = 0 := by
    rw [show H.b * H.p * H.s = H.b * H.s * H.p by ring]
    exact htriple H.b H.s H.p hs hp0
  have hbqr : (H.b * H.q * H.r).coeff j = 0 :=
    htriple H.b H.q H.r hq hr0
  have hars : (H.a * H.r * H.s).coeff j = 0 := by
    rw [show H.a * H.r * H.s = H.a * H.s * H.r by ring]
    exact htriple H.a H.s H.r hs hr0
  have hmain :
      (H.activeDet * H.y).coeff j =
        H.activeDet.coeff 0 * H.y.coeff j :=
    coeff_mul_eq_constant_mul_of_right_vanishes_below
      H.activeDet H.y hy
  unfold schurB
  rw [Polynomial.coeff_sub, hmain]
  have hcorr :
      (H.d * H.p * H.q -
          H.b * (H.p * H.s + H.q * H.r) +
          H.a * H.r * H.s).coeff j = 0 := by
    rw [show
      H.d * H.p * H.q -
            H.b * (H.p * H.s + H.q * H.r) +
            H.a * H.r * H.s =
        H.d * H.p * H.q - H.b * H.p * H.s -
          H.b * H.q * H.r + H.a * H.r * H.s by ring]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
    rw [hdpq, hbps, hbqr, hars]
    ring
  rw [hcorr]
  simp

end GeneralFourBlock

end

end HC4.Newton
