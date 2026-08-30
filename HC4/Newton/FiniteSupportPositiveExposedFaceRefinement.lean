import HC4.Newton.FiniteSupportExposedFaceRefinement
import Mathlib.Tactic

/-!
# Positive finite exposed-face refinement

A signed secondary Newton weight may be needed to isolate a smaller face, while
reverse-Rees covariance requires the final coordinate weights and determinant
clock to be positive.  On finite support these requirements are compatible:
start with a positive primary exposure carrying a positive four-dimensional
Hessian clock and choose its lexicographic scale sufficiently large.

This file packages that elementary domination argument once.  It is entirely
state-free and specific only to the four source coordinates through the clock
`4*c - 2*sum w`.
-/

namespace HC4.Newton

noncomputable section

open scoped BigOperators

/-- Finsupp weight is linear in a linear combination of two `Fin 4` source
weights. -/
theorem finsupp_weight_fin4_linear_combination
    (M : ℤ) (w v : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => M * w i + v i) e =
      M * Finsupp.weight w e + Finsupp.weight v e := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · rw [Finsupp.weight_apply, Finsupp.sum_fintype]
      · rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
        push_cast
        ring
      · intro i
        simp
    · intro i
      simp
  · intro i
    simp

/-- An exposed face remains exposed after restricting the ambient support to
an intermediate set which still contains the face. -/
theorem IsExposedFace.restrict_ambient
    {α : Type*}
    {S F G : Set α} {w : α → ℤ} {c : ℤ}
    (hG : IsExposedFace S G w c)
    (hGF : G ⊆ F)
    (hFS : F ⊆ S) :
    IsExposedFace F G w c := by
  constructor
  · ext x
    constructor
    · intro hxG
      exact ⟨hGF hxG, hG.weight_eq hxG⟩
    · rintro ⟨hxF, hw⟩
      exact hG.mem_iff.mpr ⟨hFS hxF, hw⟩
  · intro x hxF
    exact hG.weight_le (hFS hxF)

/-- **Positive four-dimensional refinement.**

Suppose a finite source support is first exposed by a strictly positive integer
source weight `w` at a positive level `c`, and its Hessian covariance clock
`4*c - 2*sum w` is positive.  Any further signed exposure `v,d` inside that
face can be absorbed into one sufficiently large natural multiple of the
primary weight.  The resulting direct weight still has positive coordinates,
positive level, and positive Hessian clock. -/
theorem exists_nat_refine_exposed_face_fin4_positive_clock
    (S : Finset (Fin 4 →₀ ℕ)) (hS : S.Nonempty)
    {F G : Set (Fin 4 →₀ ℕ)}
    {w v : Fin 4 → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) F
      (fun x => Finsupp.weight w x) c)
    (hG : IsExposedFace F G
      (fun x => Finsupp.weight v x) d)
    (hwpos : ∀ i : Fin 4, 0 < w i)
    (hcpos : 0 < c)
    (hclock : 0 < 4 * c - 2 * ∑ i : Fin 4, w i) :
    ∃ M : ℕ,
      0 < M ∧
      IsExposedFace (↑S : Set (Fin 4 →₀ ℕ)) G
        (fun x =>
          Finsupp.weight (fun i => (M : ℤ) * w i + v i) x)
        ((M : ℤ) * c + d) ∧
      (∀ i : Fin 4, 0 < (M : ℤ) * w i + v i) ∧
      0 < (M : ℤ) * c + d ∧
      0 <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
  let eps : ℤ := 4 * d - 2 * ∑ i : Fin 4, v i
  let gain : Fin 6 → ℤ :=
    ![-v 0, -v 1, -v 2, -v 3, -d, -eps]
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
  have hgeps : -eps < (B : ℤ) := by
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
    have hnonneg :
        0 ≤ (M : ℤ) * (w i - 1) :=
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
  have hdelta : 0 < delta := by simpa [delta] using hclock
  have hMdelta : (M : ℤ) ≤ (M : ℤ) * delta := by
    have hdeltaOne : (1 : ℤ) ≤ delta := by omega
    have hnonneg : 0 ≤ (M : ℤ) * (delta - 1) :=
      mul_nonneg (le_of_lt hMz) (by omega)
    nlinarith
  have hepsM : -eps < (M : ℤ) := lt_of_lt_of_le hgeps hBMz
  have hclockEq :
      4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) =
        (M : ℤ) * delta + eps := by
    dsimp [delta, eps]
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four]
    ring
  have hclockFinal :
      0 <
        4 * ((M : ℤ) * c + d) -
          2 * ∑ i : Fin 4, ((M : ℤ) * w i + v i) := by
    rw [hclockEq]
    linarith

  exact ⟨M, hMpos, hface, hcoord, hlevel, hclockFinal⟩

end

end HC4.Newton