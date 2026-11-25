import HC4.Polynomial.RationalCharacteristicRankOneClosure
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The remaining rank-two rational characteristic case

A nonzero two-by-two minor forces rank at least two. Cube-zero
then forces a nonzero square of rank at most one. In particular
a nonzero column of the square gives a genuine rational
derivation that annihilates the entire velocity field.

This is a reduction of the remaining rigidity case, not a
classification of rank-two rational characteristic fields.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section MatrixAlgebra

variable {F : Type*} [Field F]

/-- Selecting two rows and columns is a product of rectangular
selector matrices, so a nonzero minor forces rank at least two. -/
theorem rankTwo_rank_ge_two_of_minor
    (N : Matrix (Fin 3) (Fin 3) F) (a b i j : Fin 3)
    (hm : N a i * N b j ≠ N a j * N b i) : 2 ≤ N.rank := by
  classical
  let r : Fin 2 → Fin 3 := ![a, b]
  let c : Fin 2 → Fin 3 := ![i, j]
  let P : Matrix (Fin 2) (Fin 3) F := fun u k => if k = r u then 1 else 0
  let Q : Matrix (Fin 3) (Fin 2) F := fun k v => if k = c v then 1 else 0
  let A : Matrix (Fin 2) (Fin 2) F := N.submatrix r c
  have hp (u : Fin 2) (v : Fin 3) : (P * N) u v = N (r u) v := by
    change (∑ k : Fin 3, (if k = r u then 1 else 0) * N k v) = _
    rw [Finset.sum_eq_single (r u)]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hA : (P * N) * Q = A := by
    apply Matrix.ext
    intro u v
    change (∑ k : Fin 3, (P * N) u k * (if k = c v then 1 else 0)) =
      N (r u) (c v)
    rw [Finset.sum_eq_single (c v)]
    · simp [hp]
    · intro k _ hk
      simp [hk]
    · simp
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    change N a i * N b j - N a j * N b i ≠ 0
    exact sub_ne_zero.mpr hm
  have hr : A.rank = 2 := by
    have h := Matrix.rank_mul_eq_right_of_isUnit_det A
      (1 : Matrix (Fin 2) (Fin 2) F) (isUnit_iff_ne_zero.mpr hdet)
    rw [Matrix.mul_one, Matrix.rank_one, Fintype.card_fin] at h
    exact h
  calc
    2 = A.rank := hr.symm
    _ ≤ (P * N).rank := by rw [← hA]; exact Matrix.rank_mul_le_left _ _
    _ ≤ N.rank := Matrix.rank_mul_le_right _ _

/-- Cube-zero in dimension three and a nonzero minor isolate the
nonzero rank-one square. The proof is pure rank-nullity. -/
theorem rankTwo_square_frontier
    (N : Matrix (Fin 3) (Fin 3) F)
    (h3 : N ^ 3 = 0)
    (hm : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i) :
    2 ≤ N.rank ∧ N * N ≠ 0 ∧ (N * N).rank ≤ 1 ∧
      N * (N * N) = 0 ∧ (N * N) * N = 0 := by
  obtain ⟨a, b, i, j, hm⟩ := hm
  have hr := rankTwo_rank_ge_two_of_minor N a b i j hm
  have hleft : N * (N * N) = 0 := by
    simpa only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc] using h3
  have hright : (N * N) * N = 0 := by
    rw [Matrix.mul_assoc]
    exact hleft
  have hs : N * N ≠ 0 := by
    intro hz
    have hh := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
    rw [Fintype.card_fin] at hh
    omega
  have hsmall := Matrix.rank_add_rank_le_card_of_mul_eq_zero hleft
  rw [Fintype.card_fin] at hsmall
  exact ⟨hr, hs, by omega, hleft, hright⟩

end MatrixAlgebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3

/-- Directional derivative with rational coefficients in the
original transverse coordinate system. -/
def rankTwo_directionalDerivation (w : Fin 3 → E K) :
    Derivation K (E K) (E K) :=
  ∑ j : Fin 3, w j • rationalCharacteristicPartial j

theorem rankTwo_directionalDerivation_apply
    (w : Fin 3 → E K) (z : E K) :
    rankTwo_directionalDerivation w z =
      ∑ j : Fin 3, w j * rationalCharacteristicPartial j z := by
  classical
  simp [rankTwo_directionalDerivation, Derivation.sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- The directional derivative acts on the original coordinate
functions by its components; a nonzero direction is not the zero
derivation. -/
theorem rankTwo_directionalDerivation_X
    (w : Fin 3 → E K) (i : Fin 3) :
    rankTwo_directionalDerivation w (algebraMap (B K) (E K) (X i)) = w i := by
  classical
  rw [rankTwo_directionalDerivation_apply]
  simp only [rationalCharacteristicPartial_algebraMap]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_X_of_ne hj.symm, map_zero, mul_zero]
  · simp

/-- The square of the characteristic Jacobian provides a nonzero
direction annihilating every element of the actual velocity field
whenever the already-closed rank-at-most-one case fails. -/
theorem rankTwo_exists_velocityField_kernelDirection
    (V : I → E K)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ w : Fin 3 → E K, w ≠ 0 ∧
      rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      ∀ z ∈ IntermediateField.adjoin K (Set.range (fun a : Fin 3 => V (.inr a))),
        rankTwo_directionalDerivation w z = 0 := by
  classical
  let N := rationalCharacteristicJacobian V
  have hminor : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h ⟨a, i, b, j, hz⟩
  obtain ⟨_, hs, _, hl, _⟩ := rankTwo_square_frontier N h3 hminor
  have hentry : ∃ i j : Fin 3, (N * N) i j ≠ 0 := by
    by_contra h
    apply hs
    apply Matrix.ext
    intro i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hentry
  let w : Fin 3 → E K := fun k => (N * N) k j
  have hw : w ≠ 0 := by
    intro h
    exact hij (congrFun h i)
  have hker : N *ᵥ w = 0 := by
    funext k
    exact congrArg (fun A : Matrix (Fin 3) (Fin 3) (E K) => A k j) hl
  refine ⟨w, hw, hker, ?_⟩
  intro z hz
  apply rationalDerivation_zero_of_mem_adjoin (rankTwo_directionalDerivation w) _ _ z hz
  rintro x ⟨k, rfl⟩
  rw [rankTwo_directionalDerivation_apply]
  have he := congrFun hker k
  change (∑ l : Fin 3, N k l * w l) = 0 at he
  simpa only [N, rationalCharacteristicJacobian, mul_comm] using he

end
end HC4.Polynomial.RankThreeCubic
