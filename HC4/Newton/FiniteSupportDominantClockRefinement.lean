import HC4.Newton.FiniteSupportPositiveExposedFaceRefinement
import Mathlib.Tactic

/-!
# Finite exposed-face refinement with determinant clock above source level

The positive refinement theorem keeps the final coordinate weights, source
level, and four-dimensional Hessian clock positive.  In the strict-low HC4
branch the primary contact has a stronger property: its determinant clock is
strictly larger than its source level.  Since the secondary exposure is finite,
that strict margin can also be preserved by choosing the lexicographic scale
sufficiently large.

This state-free lemma records exactly that strengthening.
-/

namespace HC4.Newton

noncomputable section

open scoped BigOperators

/-- **Dominant-clock finite refinement.**  If the primary four-dimensional
Hessian clock is strictly above its source level, then a sufficiently large
lexicographic refinement preserves that strict inequality while still making
all final coordinate weights and the final source level positive. -/
theorem exists_nat_refine_exposed_face_fin4_clock_gt_level
    (S : Finset (Fin 4 →₀ ℕ)) (hS : S.Nonempty)
    {F G : Set (Fin 4 →₀ ℕ)}
    {w v : Fin 4 → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) F
      (fun x => Finsupp.weight w x) c)
    (hG : IsExposedFace F G
      (fun x => Finsupp.weight v x) d)
    (hwpos : ∀ i : Fin 4, 0 < w i)
    (hcpos : 0 < c)
    (hdominant :
      c < 4 * c - 2 * ∑ i : Fin 4, w i) :
    ∃ M : ℕ,
      0 < M ∧
      IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) G
        (fun x =>
          Finsupp.weight (fun i => (M : ℤ) * w i + v i) x)
        ((M : ℤ) * c + d) ∧
      (∀ i : Fin 4, 0 < (M : ℤ) * w i + v i) ∧
      0 < (M : ℤ) * c + d ∧
      (M : ℤ) * c + d <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
  let eps : ℤ := 4 * d - 2 * ∑ i : Fin 4, v i
  let gain : Fin 6 → ℤ :=
    ![-v 0, -v 1, -v 2, -v 3, -d, d - eps]
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
  have hgmargin : d - eps < (B : ℤ) := by
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
    have hwi : (1 : ℤ) ≤ w i := by omega
    have hnonneg : 0 ≤ (M : ℤ) * (w i - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hcoord : ∀ i : Fin 4, 0 < (M : ℤ) * w i + v i := by
    intro i
    fin_cases i
    · have hneg : -v 0 < (M : ℤ) := lt_of_lt_of_le hg0 hBMz
      linarith [hM_mul_weight 0]
    · have hneg : -v 1 < (M : ℤ) := lt_of_lt_of_le hg1 hBMz
      linarith [hM_mul_weight 1]
    · have hneg : -v 2 < (M : ℤ) := lt_of_lt_of_le hg2 hBMz
      linarith [hM_mul_weight 2]
    · have hneg : -v 3 < (M : ℤ) := lt_of_lt_of_le hg3 hBMz
      linarith [hM_mul_weight 3]

  have hMc : (M : ℤ) ≤ (M : ℤ) * c := by
    have hc : (1 : ℤ) ≤ c := by omega
    have hnonneg : 0 ≤ (M : ℤ) * (c - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hdM : -d < (M : ℤ) := lt_of_lt_of_le hgd hBMz
  have hlevel : 0 < (M : ℤ) * c + d := by
    linarith

  let delta : ℤ := 4 * c - 2 * ∑ i : Fin 4, w i
  have hmarginPrimary : 0 < delta - c := by
    dsimp [delta]
    omega
  have hMmargin : (M : ℤ) ≤ (M : ℤ) * (delta - c) := by
    have hone : (1 : ℤ) ≤ delta - c := by omega
    have hnonneg : 0 ≤ (M : ℤ) * ((delta - c) - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hsecondaryMargin : d - eps < (M : ℤ) :=
    lt_of_lt_of_le hgmargin hBMz
  have hclockEq :
      4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) =
        (M : ℤ) * delta + eps := by
    dsimp [delta, eps]
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    ring
  have hdominantFinal :
      (M : ℤ) * c + d <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
    rw [hclockEq]
    have : 0 < (M : ℤ) * (delta - c) + (eps - d) := by
      linarith
    linarith

  exact ⟨M, hMpos, hface, hcoord, hlevel, hdominantFinal⟩

end

end HC4.Newton
