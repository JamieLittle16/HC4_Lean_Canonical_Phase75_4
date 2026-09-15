import HC4.Newton.ExposedFaces
import Mathlib.Tactic

/-!
# Finite ray-to-planar ratio wall

This module packages the finite combinatorial step used by the second neutral
A19 refinement.

Suppose `R` is a distinguished subset of a finite support `S`.  Two integer
functions `p` and `s` are constant on `R`, while every point outside `R` has
strictly larger `p`.  Among the finitely many outside points choose one with
maximal centred slope

    (s-s₀)/(p-p₀).

Cross-multiplication then gives an integer weight which is zero on all of `R`
and on the selected outside point and nonpositive on all of `S`.  Its zero set
is therefore an exposed face containing `R` strictly.

In the HC4 application `p` is pair degree and `s` is the independent neutral
skew.  The resulting integer wall is itself a linear combination of the two
neutral directions, so it remains Hessian-clock neutral.
-/

namespace HC4.Newton

noncomputable section

variable {α : Type*}

/-- Centred integer wall determined by a selected point `a` and two affine
statistics `p,s`. -/
def ratioWallWeight
    (p s : α → ℤ) (p₀ s₀ : ℤ) (a x : α) : ℤ :=
  (p a - p₀) * (s x - s₀) -
    (s a - s₀) * (p x - p₀)

@[simp]
theorem ratioWallWeight_self
    (p s : α → ℤ) (p₀ s₀ : ℤ) (a : α) :
    ratioWallWeight p s p₀ s₀ a a = 0 := by
  simp [ratioWallWeight]
  ring

/-- Any point at the distinguished affine values lies on every ratio wall. -/
theorem ratioWallWeight_eq_zero_of_eq_base
    (p s : α → ℤ) (p₀ s₀ : ℤ) (a x : α)
    (hp : p x = p₀) (hs : s x = s₀) :
    ratioWallWeight p s p₀ s₀ a x = 0 := by
  simp [ratioWallWeight, hp, hs]

/-- **Finite maximal-ratio wall.**

If `p,s` are constant on `R`, every point of `S \ R` has `p>p₀`, and there is
at least one such point, then some outside point `a` determines an exposed
zero wall containing all of `R` and `a`.

The theorem deliberately returns the explicit `ratioWallWeight`; later source
code can linearise it back into coordinate weights without any choice of a
real/rational perturbation parameter. -/
theorem exists_exposed_ratio_wall
    (S : Finset α) (R : Set α)
    (p s : α → ℤ) (p₀ s₀ : ℤ)
    (hR : R ⊆ (↑S : Set α))
    (hpR : ∀ x ∈ R, p x = p₀)
    (hsR : ∀ x ∈ R, s x = s₀)
    (hoff : ∀ x ∈ S, x ∉ R → p₀ < p x)
    (hexit : ∃ x ∈ S, x ∉ R) :
    ∃ a : α,
      a ∈ S ∧ a ∉ R ∧
      IsExposedFace
        (↑S : Set α)
        {x | x ∈ (↑S : Set α) ∧
          ratioWallWeight p s p₀ s₀ a x = 0}
        (ratioWallWeight p s p₀ s₀ a) 0 ∧
      R ⊆ {x | x ∈ (↑S : Set α) ∧
        ratioWallWeight p s p₀ s₀ a x = 0} ∧
      a ∈ {x | x ∈ (↑S : Set α) ∧
        ratioWallWeight p s p₀ s₀ a x = 0} := by
  classical
  let U : Finset α := S.filter fun x => x ∉ R
  have hU : U.Nonempty := by
    rcases hexit with ⟨x, hxS, hxR⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxS, hxR⟩⟩
  let slope : α → ℚ := fun x =>
    ((s x - s₀ : ℤ) : ℚ) / ((p x - p₀ : ℤ) : ℚ)
  rcases Finset.exists_max_image U slope hU with
    ⟨a, haU, hmax⟩
  have haS : a ∈ S := (Finset.mem_filter.mp haU).1
  have haR : a ∉ R := (Finset.mem_filter.mp haU).2
  have hpa : p₀ < p a := hoff a haS haR

  have hwall_le :
      ∀ x ∈ S, ratioWallWeight p s p₀ s₀ a x ≤ 0 := by
    intro x hxS
    by_cases hxR : x ∈ R
    · rw [ratioWallWeight_eq_zero_of_eq_base
          p s p₀ s₀ a x (hpR x hxR) (hsR x hxR)]
    · have hpx : p₀ < p x := hoff x hxS hxR
      have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hxS, hxR⟩
      have hslope : slope x ≤ slope a := hmax x hxU
      have hpxQ : (0 : ℚ) < ((p x - p₀ : ℤ) : ℚ) := by
        exact_mod_cast (sub_pos.mpr hpx)
      have hpaQ : (0 : ℚ) < ((p a - p₀ : ℤ) : ℚ) := by
        exact_mod_cast (sub_pos.mpr hpa)
      have hcrossQ :
          ((s x - s₀ : ℤ) : ℚ) * ((p a - p₀ : ℤ) : ℚ) ≤
            ((s a - s₀ : ℤ) : ℚ) * ((p x - p₀ : ℤ) : ℚ) := by
        dsimp [slope] at hslope
        rw [div_le_div_iff₀ hpxQ hpaQ] at hslope
        exact hslope
      have hcrossZ :
          (s x - s₀) * (p a - p₀) ≤
            (s a - s₀) * (p x - p₀) := by
        exact_mod_cast hcrossQ
      dsimp [ratioWallWeight]
      nlinarith [hcrossZ]

  let G : Set α :=
    {x | x ∈ (↑S : Set α) ∧ ratioWallWeight p s p₀ s₀ a x = 0}
  have hface :
      IsExposedFace (↑S : Set α) G
        (ratioWallWeight p s p₀ s₀ a) 0 := by
    constructor
    · rfl
    · intro x hxS
      exact hwall_le x (by simpa using hxS)
  have hRG : R ⊆ G := by
    intro x hxR
    refine ⟨hR hxR, ?_⟩
    exact ratioWallWeight_eq_zero_of_eq_base
      p s p₀ s₀ a x (hpR x hxR) (hsR x hxR)
  have haG : a ∈ G := by
    exact ⟨by simpa using haS, ratioWallWeight_self p s p₀ s₀ a⟩
  exact ⟨a, haS, haR, hface, hRG, haG⟩

end

end HC4.Newton
