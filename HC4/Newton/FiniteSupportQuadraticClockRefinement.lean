import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import Mathlib.Tactic

/-!
# Finite exposed-face refinement with a quadratic determinant-clock margin

For the final staircase equation it is useful that not only each source layer,
but every sum of two source-layer orders, occurs before Hessian determinant
closure.  Since all source orders of a bounded reverse Rees are at most its
level, the right invariant is

    2 * level < determinantClock.

A finite signed secondary exposure can preserve this strict primary margin by
choosing the lexicographic scale sufficiently large.
-/

namespace HC4.Newton

noncomputable section

open scoped BigOperators

/-- **Quadratic-clock finite refinement.**  If twice the primary source level
is strictly below the four-dimensional Hessian clock, then some sufficiently
large finite refinement preserves that inequality together with positivity of
all final coordinate weights and of the final level. -/
theorem exists_nat_refine_exposed_face_fin4_two_level_lt_clock
    (S : Finset (Fin 4 →₀ ℕ)) (hS : S.Nonempty)
    {F G : Set (Fin 4 →₀ ℕ)}
    {w v : Fin 4 → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) F
      (fun x => Finsupp.weight w x) c)
    (hG : IsExposedFace F G
      (fun x => Finsupp.weight v x) d)
    (hwpos : ∀ i : Fin 4, 0 < w i)
    (hcpos : 0 < c)
    (hquadratic :
      2 * c < 4 * c - 2 * ∑ i : Fin 4, w i) :
    ∃ M : ℕ,
      0 < M ∧
      IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) G
        (fun x =>
          Finsupp.weight (fun i => (M : ℤ) * w i + v i) x)
        ((M : ℤ) * c + d) ∧
      (∀ i : Fin 4, 0 < (M : ℤ) * w i + v i) ∧
      0 < (M : ℤ) * c + d ∧
      2 * ((M : ℤ) * c + d) <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
  let eps : ℤ := 4 * d - 2 * ∑ i : Fin 4, v i
  let gain : Fin 6 → ℤ :=
    ![-v 0, -v 1, -v 2, -v 3, -d, 2 * d - eps]
  have huniv : (Finset.univ : Finset (Fin 6)).Nonempty := by simp
  rcases exists_positive_nat_strict_upper_bound_on_finset
      (Finset.univ : Finset (Fin 6)) huniv gain with
    ⟨B, hBpos, hgain⟩
  have hg0 : -v 0 < (B : ℤ) := by
    simpa [gain] using hgain (0 : Fin 6) (by simp)
  have hg1 : -v 1 < (B : ℤ) := by
    simpa [gain] using hgain (1 : Fin 6) (by simp)
  have hg2 : -v 2 < (B : ℤ) := by
    simpa [gain] using hgain (2 : Fin 6) (by simp)
  have hg3 : -v 3 < (B : ℤ) := by
    simpa [gain] using hgain (3 : Fin 6) (by simp)
  have hgd : -d < (B : ℤ) := by
    simpa [gain] using hgain (4 : Fin 6) (by simp)
  have hgmargin : 2 * d - eps < (B : ℤ) := by
    simpa [gain] using hgain (5 : Fin 6) (by simp)

  rcases exists_nat_refine_exposed_face_ge S hS hF hG B with
    ⟨M, hBM, hMpos, hfaceRaw⟩
  have hBMz : (B : ℤ) ≤ (M : ℤ) := by exact_mod_cast hBM
  have hMz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  have hface :
      IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) G
        (fun x =>
          Finsupp.weight (fun i => (M : ℤ) * w i + v i) x)
        ((M : ℤ) * c + d) := by
    simpa only [finsupp_weight_fin4_linear_combination] using hfaceRaw

  have hM_mul_weight : ∀ i : Fin 4, (M : ℤ) ≤ (M : ℤ) * w i := by
    intro i
    have hwi0 : (0 : ℤ) < w i := hwpos i
    have hwi : (1 : ℤ) ≤ w i := by omega
    have hnonneg : 0 ≤ (M : ℤ) * (w i - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hneg : ∀ i : Fin 4, -v i < (M : ℤ) := by
    intro i
    fin_cases i
    · exact lt_of_lt_of_le hg0 hBMz
    · exact lt_of_lt_of_le hg1 hBMz
    · exact lt_of_lt_of_le hg2 hBMz
    · exact lt_of_lt_of_le hg3 hBMz
  have hcoord : ∀ i : Fin 4, 0 < (M : ℤ) * w i + v i := by
    intro i
    have hMi := hM_mul_weight i
    have hvi := hneg i
    linarith

  have hMc : (M : ℤ) ≤ (M : ℤ) * c := by
    have hc : (1 : ℤ) ≤ c := by omega
    have hnonneg : 0 ≤ (M : ℤ) * (c - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hdM : -d < (M : ℤ) := lt_of_lt_of_le hgd hBMz
  have hlevel : 0 < (M : ℤ) * c + d := by
    linarith

  let delta : ℤ := 4 * c - 2 * ∑ i : Fin 4, w i
  have hmarginPrimary : 0 < delta - 2 * c := by
    dsimp [delta]
    omega
  have hMmargin : (M : ℤ) ≤ (M : ℤ) * (delta - 2 * c) := by
    have hone : (1 : ℤ) ≤ delta - 2 * c := by omega
    have hnonneg : 0 ≤ (M : ℤ) * ((delta - 2 * c) - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hsecondaryMargin : 2 * d - eps < (M : ℤ) :=
    lt_of_lt_of_le hgmargin hBMz
  have hclockEq :
      4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) =
        (M : ℤ) * delta + eps := by
    dsimp [delta, eps]
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    ring
  have hquadraticFinal :
      2 * ((M : ℤ) * c + d) <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
    rw [hclockEq]
    have : 0 < (M : ℤ) * (delta - 2 * c) + (eps - 2 * d) := by
      linarith
    linarith

  exact ⟨M, hMpos, hface, hcoord, hlevel, hquadraticFinal⟩

end

end HC4.Newton