import Mathlib

/-!
# Abstract exposed-face calculus

This module supplies the support-level geometry needed before introducing a
particular multivariate-polynomial representation.  An exposed face consists
of the points of a support `S` on which an integer-valued weight reaches a
specified upper level.

The main theorem is the perturbation/refinement lemma: if `F` is exposed in
`S`, `G` is exposed in `F`, and an explicit domination inequality separates
`S \ F`, then the combined weight `M*w + v` exposes `G` directly in `S`.
This is the formal finite-support version of lexicographically refining a
Newton face by a sufficiently small secondary perturbation.
-/

namespace HC4.Newton

variable {α : Type*}

/-- `F` is the level-`c` upper exposed face of `S` for the weight `w`. -/
def IsExposedFace (S F : Set α) (w : α → ℤ) (c : ℤ) : Prop :=
  F = {x | x ∈ S ∧ w x = c} ∧ ∀ x ∈ S, w x ≤ c

/-- Every exposed face is contained in its ambient support. -/
theorem IsExposedFace.subset
    {S F : Set α} {w : α → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) :
    F ⊆ S := by
  rintro x hx
  rw [hF.1] at hx
  exact hx.1

/-- Membership in an exposed face is ambient membership plus level equality. -/
theorem IsExposedFace.mem_iff
    {S F : Set α} {w : α → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) {x : α} :
    x ∈ F ↔ x ∈ S ∧ w x = c := by
  simpa [hF.1]

/-- All ambient support points lie weakly below the exposing level. -/
theorem IsExposedFace.weight_le
    {S F : Set α} {w : α → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) {x : α} (hx : x ∈ S) :
    w x ≤ c :=
  hF.2 x hx

/-- An exposed point attains the exposing level. -/
theorem IsExposedFace.weight_eq
    {S F : Set α} {w : α → ℤ} {c : ℤ}
    (hF : IsExposedFace S F w c) {x : α} (hx : x ∈ F) :
    w x = c :=
  (hF.mem_iff.mp hx).2

/-- A weight constant on `S` exposes all of `S`. -/
theorem exposedFace_self
    (S : Set α) (w : α → ℤ) (c : ℤ)
    (hconst : ∀ x ∈ S, w x = c) :
    IsExposedFace S S w c := by
  constructor
  · ext x
    constructor
    · intro hx
      exact ⟨hx, hconst x hx⟩
    · exact fun hx => hx.1
  · intro x hx
    exact (hconst x hx).le

/-- The intersection of two faces exposed in the same support is exposed by the sum weight. -/
theorem intersection_exposed
    {S F G : Set α} {w v : α → ℤ} {c d : ℤ}
    (hF : IsExposedFace S F w c)
    (hG : IsExposedFace S G v d) :
    IsExposedFace S (F ∩ G) (fun x => w x + v x) (c + d) := by
  constructor
  · ext x
    constructor
    · rintro ⟨hxF, hxG⟩
      have hxS : x ∈ S := hF.subset hxF
      have hw : w x = c := hF.weight_eq hxF
      have hv : v x = d := hG.weight_eq hxG
      exact ⟨hxS, by linarith⟩
    · rintro ⟨hxS, hsum⟩
      have hwLe : w x ≤ c := hF.weight_le hxS
      have hvLe : v x ≤ d := hG.weight_le hxS
      have hw : w x = c := by linarith
      have hv : v x = d := by linarith
      exact ⟨hF.mem_iff.mpr ⟨hxS, hw⟩, hG.mem_iff.mpr ⟨hxS, hv⟩⟩
  · intro x hxS
    have hwLe : w x ≤ c := hF.weight_le hxS
    have hvLe : v x ≤ d := hG.weight_le hxS
    linarith

/-- Positive integer rescaling does not change an exposed face. -/
theorem scale_exposed
    {S F : Set α} {w : α → ℤ} {c m : ℤ}
    (hm : 0 < m) (hF : IsExposedFace S F w c) :
    IsExposedFace S F (fun x => m * w x) (m * c) := by
  constructor
  · ext x
    constructor
    · intro hxF
      have hxS : x ∈ S := hF.subset hxF
      have hw : w x = c := hF.weight_eq hxF
      refine ⟨hxS, ?_⟩
      change m * w x = m * c
      rw [hw]
    · rintro ⟨hxS, hmul⟩
      have hm0 : m ≠ 0 := ne_of_gt hm
      have hw : w x = c := by
        exact mul_left_cancel₀ hm0 hmul
      exact hF.mem_iff.mpr ⟨hxS, hw⟩
  · intro x hxS
    exact mul_le_mul_of_nonneg_left (hF.weight_le hxS) hm.le

/--
Lexicographic exposed-face refinement with an explicit domination bound.

`F` is first exposed in `S` by `w` at `c`; `G` is then exposed inside `F` by
`v` at `d`.  The gap condition says that the primary loss away from `F`, after
multiplication by `M`, dominates every possible secondary gain.  Then
`M*w+v` exposes `G` directly in `S`.
-/
theorem refine_exposed_face
    {S F G : Set α} {w v : α → ℤ} {c d M : ℤ}
    (hF : IsExposedFace S F w c)
    (hG : IsExposedFace F G v d)
    (hgap : ∀ x ∈ S, x ∉ F → v x - d < M * (c - w x)) :
    IsExposedFace S G (fun x => M * w x + v x) (M * c + d) := by
  constructor
  · ext x
    constructor
    · intro hxG
      have hxF : x ∈ F := hG.subset hxG
      have hxS : x ∈ S := hF.subset hxF
      have hw : w x = c := hF.weight_eq hxF
      have hv : v x = d := hG.weight_eq hxG
      refine ⟨hxS, ?_⟩
      change M * w x + v x = M * c + d
      rw [hw, hv]
    · rintro ⟨hxS, hlevel⟩
      have hxF : x ∈ F := by
        by_contra hxNot
        have hstrict := hgap x hxS hxNot
        linarith
      have hw : w x = c := hF.weight_eq hxF
      have hv : v x = d := by
        change M * w x + v x = M * c + d at hlevel
        rw [hw] at hlevel
        linarith
      exact hG.mem_iff.mpr ⟨hxF, hv⟩
  · intro x hxS
    by_cases hxF : x ∈ F
    · have hw : w x = c := hF.weight_eq hxF
      have hvLe : v x ≤ d := hG.weight_le hxF
      change M * w x + v x ≤ M * c + d
      rw [hw]
      linarith
    · have hstrict := hgap x hxS hxF
      linarith

/-- Refinement recovers the nested face exactly, not merely a subset. -/
theorem refine_exposed_face_membership
    {S F G : Set α} {w v : α → ℤ} {c d M : ℤ}
    (hF : IsExposedFace S F w c)
    (hG : IsExposedFace F G v d)
    (hgap : ∀ x ∈ S, x ∉ F → v x - d < M * (c - w x))
    {x : α} :
    x ∈ G ↔ x ∈ S ∧ M * w x + v x = M * c + d := by
  exact (refine_exposed_face hF hG hgap).mem_iff

end HC4.Newton
