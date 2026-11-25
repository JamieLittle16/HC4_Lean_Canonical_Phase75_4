import HC4.Polynomial.RationalCharacteristicRankOneCommonParameter
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Rank-one differential invariants of the velocity field

Instead of assuming an algebraic parametrization, choose a genuine
nonzero Jacobian pivot. The two transverse derivations corrected
by the pivot direction kill the three actual velocities, and
therefore their entire generated intermediate field.

This is the input for specialization of that field to a coordinate
line: away from pivot poles and zeros the corrected transverse
derivations are regular and have unit normal component.

No specialization injectivity or Lüroth theorem is assumed here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The constants of any ground-field derivation form an intermediate
field, without any characteristic or dimension restriction. -/
def rationalDerivation_constantField (D : Derivation K F F) :
    IntermediateField K F where
  carrier := {x | D x = 0}
  zero_mem' := D.map_zero
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x * y) = 0
    simp only [Derivation.leibniz, hx, hy, smul_zero, add_zero]
  neg_mem' := by
    intro x hx
    change D x = 0 at hx
    change D (-x) = 0
    rw [map_neg, hx, neg_zero]
  inv_mem' := by
    intro x hx
    change D x = 0 at hx
    change D x⁻¹ = 0
    by_cases hn : x = 0
    · simp [hn]
    · have h := congrArg D (mul_inv_cancel₀ hn)
      change D (x * x⁻¹) = D 1 at h
      rw [Derivation.leibniz, D.map_one_eq_zero, hx, smul_zero, add_zero] at h
      change x * D x⁻¹ = 0 at h
      exact (mul_eq_zero.mp h).resolve_left hn
  algebraMap_mem' := fun a => D.map_algebraMap a

/-- All field combinations of invariants remain invariant. -/
theorem rationalDerivation_zero_of_mem_adjoin
    (D : Derivation K F F) (s : Set F)
    (hs : ∀ x ∈ s, D x = 0)
    (z : F) (hz : z ∈ IntermediateField.adjoin K s) :
    D z = 0 := by
  have h : IntermediateField.adjoin K s ≤ rationalDerivation_constantField D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    exact hs x hx
  exact h hz

variable {k : Type*} [Field k]

private abbrev B (k : Type*) [Field k] := MvPolynomial (Fin 3) k
private abbrev E (k : Type*) [Field k] := FractionRing (B k)
private abbrev I := Unit ⊕ Fin 3

/-- Correct a coordinate derivative by the chosen nonzero pivot
direction. This is an actual derivation, not merely a pointwise
linear differential constraint. -/
def rankOne_correctedPartial (V : I → E k) (i j l : Fin 3) :
    Derivation k (E k) (E k) :=
  rationalCharacteristicPartial l -
    (rationalCharacteristicJacobian V i l /
      rationalCharacteristicJacobian V i j) • rationalCharacteristicPartial j

/-- The vanishing 2x2 minors make every velocity invariant under
each corrected derivative. -/
theorem rankOne_correctedPartial_velocity_zero
    (V : I → E k) (i j l a : Fin 3)
    (hp : rationalCharacteristicJacobian V i j ≠ 0)
    (hm : ∀ a b : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    rankOne_correctedPartial V i j l (V (.inr a)) = 0 := by
  let N := rationalCharacteristicJacobian V
  change N a l - (N i l / N i j) * N a j = 0
  apply (mul_right_cancel₀ hp)
  have he : (N a l - (N i l / N i j) * N a j) * N i j =
      N a l * N i j - N a j * N i l := by
    change (N a l - (N i l / N i j) * N a j) * N i j = _
    have hh : N i j ≠ 0 := hp
    field_simp [hh] <;> ring
  rw [he, hm a l, sub_self, zero_mul]

/-- The pivot invariance extends from the original three velocities
to every element of their generated field. -/
theorem rankOne_correctedPartial_velocityField_zero
    (V : I → E k) (i j l : Fin 3)
    (hp : rationalCharacteristicJacobian V i j ≠ 0)
    (hm : ∀ a b : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b)
    (z : E k)
    (hz : z ∈ IntermediateField.adjoin k (Set.range (fun a : Fin 3 => V (.inr a)))) :
    rankOne_correctedPartial V i j l z = 0 := by
  apply rationalDerivation_zero_of_mem_adjoin (rankOne_correctedPartial V i j l) _ _ z hz
  rintro x ⟨a, rfl⟩
  exact rankOne_correctedPartial_velocity_zero V i j l a hp hm

/-- On every transverse coordinate other than the pivot column,
the corrected derivations retain their exact normal components.
This is the key local noncharacteristic property for specialization. -/
theorem rankOne_correctedPartial_transverse_X
    (V : I → E k) (i j l a : Fin 3) (ha : a ≠ j) :
    rankOne_correctedPartial V i j l (algebraMap (B k) (E k) (X a)) =
      if a = l then 1 else 0 := by
  change rationalCharacteristicPartial l (algebraMap (B k) (E k) (X a)) -
    (rationalCharacteristicJacobian V i l /
      rationalCharacteristicJacobian V i j) *
      rationalCharacteristicPartial j (algebraMap (B k) (E k) (X a)) = _
  rw [rationalCharacteristicPartial_algebraMap, rationalCharacteristicPartial_algebraMap,
    pderiv_X_of_ne ha, map_zero, mul_zero, sub_zero]
  by_cases h : a = l
  · subst a
    simp
  · simp [pderiv_X_of_ne h, h]

/-- A nonzero rank-one matrix in minor form always supplies the
pivot required by the invariant-field construction. -/
theorem rankOne_jacobian_exists_pivot
    (V : I → E k) (hn : rationalCharacteristicJacobian V ≠ 0)
    (hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ i j : Fin 3, rationalCharacteristicJacobian V i j ≠ 0 ∧
      ∀ l : Fin 3, ∀ z ∈
        IntermediateField.adjoin k (Set.range (fun a : Fin 3 => V (.inr a))),
        rankOne_correctedPartial V i j l z = 0 := by
  classical
  have hex : ∃ i j : Fin 3, rationalCharacteristicJacobian V i j ≠ 0 := by
    by_contra h
    apply hn
    apply Matrix.ext
    intro i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hp⟩ := hex
  refine ⟨i, j, hp, ?_⟩
  intro l z hz
  exact rankOne_correctedPartial_velocityField_zero V i j l hp
    (fun a b => hm a b i j) z hz

end
end HC4.Polynomial.RankThreeCubic
