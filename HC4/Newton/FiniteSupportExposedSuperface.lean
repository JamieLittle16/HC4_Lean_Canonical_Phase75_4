import HC4.Newton.ExposedFaces
import Mathlib.Tactic

/-!
# First exposed superface from finite support

A later Newton staircase sometimes starts with a small exposed face `F` and a
second integer weight which is constant on `F` but strictly lower at some
ambient support point.  The correct next carrier is not obtained by pretending
that every lower point lies on `F`.  Instead one moves the normal vector just
far enough that `F` first meets another support point.

On finite support this is elementary.  If `F` is exposed by `w=c` and the
secondary weight is `v=d` on `F`, then for every point below both levels form

    (d - v(x)) / (c - w(x)).

Choose a point where this ratio is maximal.  If its losses are `A=d-v(x0)` and
`B=c-w(x0)`, the combined weight

    A*w - B*v

is bounded above on the whole support and is equal to its level on all of `F`
and on `x0`.  Thus it exposes a strict superface of `F`.

No claim is made about the dimension of the resulting face.  In particular,
this lemma is safe to use before the later rank/plane argument has been proved.
-/

namespace HC4.Newton

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Ambient points outside `F` at which the secondary weight drops below its
constant value on `F`. -/
noncomputable def exposedSuperfaceCandidates
    (S : Finset α) (F : Set α) (v : α → ℤ) (d : ℤ) : Finset α := by
  classical
  exact S.filter fun x => x ∉ F ∧ v x < d

@[simp]
theorem mem_exposedSuperfaceCandidates
    (S : Finset α) (F : Set α) (v : α → ℤ) (d : ℤ) (x : α) :
    x ∈ exposedSuperfaceCandidates S F v d ↔
      x ∈ S ∧ x ∉ F ∧ v x < d := by
  classical
  simp [exposedSuperfaceCandidates, and_assoc]

/-- Ratio of secondary loss to primary loss.  It is used only on candidates,
where both denominator and numerator are positive. -/
def exposedSuperfaceSlope
    (w v : α → ℤ) (c d : ℤ) (x : α) : ℚ :=
  ((d - v x : ℤ) : ℚ) / ((c - w x : ℤ) : ℚ)

/-- A finite nonempty candidate set contains a maximal expansion slope. -/
theorem exists_max_exposedSuperfaceSlope
    (S : Finset α) (F : Set α) (w v : α → ℤ) (c d : ℤ)
    (hne : (exposedSuperfaceCandidates S F v d).Nonempty) :
    ∃ x₀ ∈ exposedSuperfaceCandidates S F v d,
      ∀ x ∈ exposedSuperfaceCandidates S F v d,
        exposedSuperfaceSlope w v c d x ≤
          exposedSuperfaceSlope w v c d x₀ := by
  exact Finset.exists_max_image _ _ hne

/-- **Finite first-superface theorem.**

`F` is already an upper exposed face of the finite support `S`.  A secondary
integer weight is constant at level `d` on `F`, and at least one ambient point
strictly below that secondary level lies outside `F`.  Then a positive integer
linear combination `A*w - B*v` exposes a strict superface `G` containing all of
`F` and at least one new point.

The coefficients `A,B` are returned as positive integers in `ℤ`; this avoids
any divisibility or normalization choice. -/
theorem exists_first_exposed_superface
    (S : Finset α)
    {F : Set α} {w v : α → ℤ} {c d : ℤ}
    (hF : IsExposedFace (↑S : Set α) F w c)
    (hvF : ∀ x ∈ F, v x = d)
    (hexit : ∃ x ∈ S, x ∉ F ∧ v x < d) :
    ∃ (A B : ℤ) (G : Set α),
      0 < A ∧ 0 < B ∧
      IsExposedFace (↑S : Set α) G
        (fun x => A * w x - B * v x)
        (A * c - B * d) ∧
      F ⊆ G ∧
      ∃ x, x ∈ G ∧ x ∉ F := by
  classical
  have hcand : (exposedSuperfaceCandidates S F v d).Nonempty := by
    rcases hexit with ⟨x, hxS, hxF, hv⟩
    exact ⟨x, (mem_exposedSuperfaceCandidates S F v d x).2
      ⟨hxS, hxF, hv⟩⟩
  rcases exists_max_exposedSuperfaceSlope S F w v c d hcand with
    ⟨x₀, hx₀cand, hmax⟩
  have hx₀ := (mem_exposedSuperfaceCandidates S F v d x₀).1 hx₀cand
  have hx₀Sset : x₀ ∈ (↑S : Set α) := by simpa using hx₀.1
  have hw₀le : w x₀ ≤ c := hF.weight_le hx₀Sset
  have hw₀ne : w x₀ ≠ c := by
    intro hw
    apply hx₀.2.1
    exact hF.mem_iff.mpr ⟨hx₀Sset, hw⟩
  have hp₀ : 0 < c - w x₀ := by omega
  have hq₀ : 0 < d - v x₀ := by omega

  let A : ℤ := d - v x₀
  let B : ℤ := c - w x₀
  let G : Set α :=
    {x | x ∈ (↑S : Set α) ∧
      A * w x - B * v x = A * c - B * d}
  have hA : 0 < A := by simpa [A] using hq₀
  have hB : 0 < B := by simpa [B] using hp₀

  have hupper : ∀ x ∈ (↑S : Set α),
      A * w x - B * v x ≤ A * c - B * d := by
    intro x hxS
    have hwle : w x ≤ c := hF.weight_le hxS
    by_cases hxF : x ∈ F
    · have hw : w x = c := hF.weight_eq hxF
      have hv : v x = d := hvF x hxF
      rw [hw, hv]
    · have hwne : w x ≠ c := by
        intro hw
        exact hxF (hF.mem_iff.mpr ⟨hxS, hw⟩)
      have hp : 0 < c - w x := by omega
      by_cases hvlt : v x < d
      · have hxSfin : x ∈ S := by simpa using hxS
        have hxcand : x ∈ exposedSuperfaceCandidates S F v d :=
          (mem_exposedSuperfaceCandidates S F v d x).2
            ⟨hxSfin, hxF, hvlt⟩
        have hslope := hmax x hxcand
        have hpQ : (0 : ℚ) < ((c - w x : ℤ) : ℚ) := by exact_mod_cast hp
        have hp₀Q : (0 : ℚ) < ((c - w x₀ : ℤ) : ℚ) := by exact_mod_cast hp₀
        have hcrossQ :
            ((d - v x : ℤ) : ℚ) * ((c - w x₀ : ℤ) : ℚ) ≤
              ((d - v x₀ : ℤ) : ℚ) * ((c - w x : ℤ) : ℚ) := by
          exact (div_le_div_iff₀ hpQ hp₀Q).mp (by
            simpa [exposedSuperfaceSlope] using hslope)
        have hcross :
            (d - v x) * (c - w x₀) ≤
              (d - v x₀) * (c - w x) := by
          exact_mod_cast hcrossQ
        dsimp [A, B]
        nlinarith
      · have hvge : d ≤ v x := le_of_not_gt hvlt
        have hAw : A * w x ≤ A * c :=
          mul_le_mul_of_nonneg_left hwle (le_of_lt hA)
        have hBv : B * d ≤ B * v x :=
          mul_le_mul_of_nonneg_left hvge (le_of_lt hB)
        linarith

  have hface :
      IsExposedFace (↑S : Set α) G
        (fun x => A * w x - B * v x)
        (A * c - B * d) := by
    constructor
    · rfl
    · exact hupper

  have hFG : F ⊆ G := by
    intro x hxF
    have hxS := hF.subset hxF
    have hw := hF.weight_eq hxF
    have hv := hvF x hxF
    change x ∈ (↑S : Set α) ∧
      A * w x - B * v x = A * c - B * d
    exact ⟨hxS, by rw [hw, hv]⟩

  have hx₀G : x₀ ∈ G := by
    change x₀ ∈ (↑S : Set α) ∧
      A * w x₀ - B * v x₀ = A * c - B * d
    refine ⟨hx₀Sset, ?_⟩
    dsimp [A, B]
    ring

  exact ⟨A, B, G, hA, hB, hface, hFG, x₀, hx₀G, hx₀.2.1⟩

end

end HC4.Newton
