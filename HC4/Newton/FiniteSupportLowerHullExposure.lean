import HC4.Newton.FiniteSupportRayPlanarRefinement
import Mathlib.Tactic

/-!
# Finite lower-hull exposure from a minimal base fibre

`exists_exposed_ratio_wall` handles a distinguished fibre on which both affine
statistics are constant.  For the finite-staircase roof transition we need one
small generalisation: the primary statistic is still minimal on the base
fibre, but the secondary statistic may vary there.  We choose a base point
maximising the secondary statistic on that fibre and then maximise the usual
centred rational slope among points leaving the fibre.

The resulting ratio wall is nonpositive on the whole finite support.  Points
remaining on the base fibre are harmless because their secondary value is at
most the chosen base value.  This is exactly the lower-hull support line used
by the multi-fibre roof adapter.
-/

namespace HC4.Newton

noncomputable section

variable {α : Type*}

/-- **Finite lower-hull ratio wall with a nonconstant base fibre.**

Assume `p₀` is the minimum primary value on `S`, it is attained, and some point
has strictly larger primary value.  Then there is a base point `b` at primary
value `p₀`, maximal in the secondary statistic among that fibre, and an outside
point `a` such that the centred ratio wall through `b` and `a` exposes a face
of the whole support containing both points. -/
theorem exists_exposed_ratio_wall_from_min_fiber
    [DecidableEq α]
    (S : Finset α)
    (p s : α → ℤ) (p₀ : ℤ)
    (hpmin : ∀ x ∈ S, p₀ ≤ p x)
    (hbase : ∃ x ∈ S, p x = p₀)
    (hexit : ∃ x ∈ S, p₀ < p x) :
    ∃ b a : α,
      b ∈ S ∧ p b = p₀ ∧
      (∀ x ∈ S, p x = p₀ → s x ≤ s b) ∧
      a ∈ S ∧ p₀ < p a ∧
      IsExposedFace
        (↑S : Set α)
        {x | x ∈ (↑S : Set α) ∧
          ratioWallWeight p s p₀ (s b) a x = 0}
        (ratioWallWeight p s p₀ (s b) a) 0 ∧
      b ∈ {x | x ∈ (↑S : Set α) ∧
        ratioWallWeight p s p₀ (s b) a x = 0} ∧
      a ∈ {x | x ∈ (↑S : Set α) ∧
        ratioWallWeight p s p₀ (s b) a x = 0} := by
  classical

  let B : Finset α := S.filter fun x => p x = p₀
  have hB : B.Nonempty := by
    rcases hbase with ⟨x, hxS, hxp⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxS, hxp⟩⟩
  rcases Finset.exists_max_image B s hB with ⟨b, hbB, hbmax⟩
  have hbS : b ∈ S := (Finset.mem_filter.mp hbB).1
  have hbp : p b = p₀ := (Finset.mem_filter.mp hbB).2
  have hbmax' : ∀ x ∈ S, p x = p₀ → s x ≤ s b := by
    intro x hxS hxp
    exact hbmax x (Finset.mem_filter.mpr ⟨hxS, hxp⟩)

  let U : Finset α := S.filter fun x => p₀ < p x
  have hU : U.Nonempty := by
    rcases hexit with ⟨x, hxS, hxp⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxS, hxp⟩⟩
  let slope : α → ℚ := fun x =>
    ((s x - s b : ℤ) : ℚ) / ((p x - p₀ : ℤ) : ℚ)
  rcases Finset.exists_max_image U slope hU with
    ⟨a, haU, hamax⟩
  have haS : a ∈ S := (Finset.mem_filter.mp haU).1
  have hap : p₀ < p a := (Finset.mem_filter.mp haU).2

  have hwall_le :
      ∀ x ∈ S, ratioWallWeight p s p₀ (s b) a x ≤ 0 := by
    intro x hxS
    rcases lt_or_eq_of_le (hpmin x hxS) with hpx | hpx
    · have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hxS, hpx⟩
      have hslope : slope x ≤ slope a := hamax x hxU
      have hpxQ : (0 : ℚ) < ((p x - p₀ : ℤ) : ℚ) := by
        exact_mod_cast (sub_pos.mpr hpx)
      have hpaQ : (0 : ℚ) < ((p a - p₀ : ℤ) : ℚ) := by
        exact_mod_cast (sub_pos.mpr hap)
      have hcrossQ :
          ((s x - s b : ℤ) : ℚ) * ((p a - p₀ : ℤ) : ℚ) ≤
            ((s a - s b : ℤ) : ℚ) * ((p x - p₀ : ℤ) : ℚ) := by
        dsimp [slope] at hslope
        rw [div_le_div_iff₀ hpxQ hpaQ] at hslope
        exact hslope
      have hcrossZ :
          (s x - s b) * (p a - p₀) ≤
            (s a - s b) * (p x - p₀) := by
        exact_mod_cast hcrossQ
      dsimp [ratioWallWeight]
      nlinarith [hcrossZ]
    · have hxp : p x = p₀ := hpx.symm
      have hsx : s x ≤ s b := hbmax' x hxS hxp
      have hpa : 0 < p a - p₀ := sub_pos.mpr hap
      dsimp [ratioWallWeight]
      rw [hxp]
      nlinarith

  let G : Set α :=
    {x | x ∈ (↑S : Set α) ∧
      ratioWallWeight p s p₀ (s b) a x = 0}
  have hface :
      IsExposedFace (↑S : Set α) G
        (ratioWallWeight p s p₀ (s b) a) 0 := by
    constructor
    · rfl
    · intro x hxS
      exact hwall_le x (by simpa using hxS)

  have hbG : b ∈ G := by
    refine ⟨by simpa using hbS, ?_⟩
    exact ratioWallWeight_eq_zero_of_eq_base
      p s p₀ (s b) a b hbp rfl
  have haG : a ∈ G := by
    exact ⟨by simpa using haS,
      ratioWallWeight_self p s p₀ (s b) a⟩

  exact ⟨b, a, hbS, hbp, hbmax', haS, hap, hface, hbG, haG⟩

end

end HC4.Newton