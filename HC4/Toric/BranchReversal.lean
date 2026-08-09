import HC4.Toric.CharacterSupport

/-!
# Coordinate reversal on the symmetric invariant semigroup

The involution

    (u₁,u₂,u₃,u₄) ↦ (u₄,u₃,u₂,u₁)

preserves the original balanced grading, exchanges the `r` and `s` branches,
and negates the secondary branch character.  This is the discrete symmetry
used later to collapse reversal-stable eigen-supports to character zero.
-/

namespace HC4.Toric

/-- Reverse the four exponent coordinates. -/
def reverseExponent (u : Exponent) : Exponent :=
  ⟨u.x4, u.x3, u.x2, u.x1⟩

@[simp] theorem reverseExponent_x1 (u : Exponent) :
    (reverseExponent u).x1 = u.x4 := rfl
@[simp] theorem reverseExponent_x2 (u : Exponent) :
    (reverseExponent u).x2 = u.x3 := rfl
@[simp] theorem reverseExponent_x3 (u : Exponent) :
    (reverseExponent u).x3 = u.x2 := rfl
@[simp] theorem reverseExponent_x4 (u : Exponent) :
    (reverseExponent u).x4 = u.x1 := rfl

/-- Coordinate reversal is an involution. -/
@[simp] theorem reverseExponent_involutive (u : Exponent) :
    reverseExponent (reverseExponent u) = u := by
  ext <;> rfl

/-- Coordinate reversal is injective. -/
theorem reverseExponent_injective : Function.Injective reverseExponent :=
  Function.LeftInverse.injective reverseExponent_involutive

/-- Coordinate reversal is surjective. -/
theorem reverseExponent_surjective : Function.Surjective reverseExponent :=
  Function.RightInverse.surjective reverseExponent_involutive

/-- Coordinate reversal as an equivalence. -/
def reverseExponentEquiv : Exponent ≃ Exponent where
  toFun := reverseExponent
  invFun := reverseExponent
  left_inv := reverseExponent_involutive
  right_inv := reverseExponent_involutive

@[simp] theorem reverseExponent_pExponent :
    reverseExponent pExponent = pExponent := by
  ext <;> rfl

@[simp] theorem reverseExponent_qExponent :
    reverseExponent qExponent = qExponent := by
  ext <;> rfl

@[simp] theorem reverseExponent_rExponent (a b : ℕ) :
    reverseExponent (rExponent a b) = sExponent a b := by
  ext <;> rfl

@[simp] theorem reverseExponent_sExponent (a b : ℕ) :
    reverseExponent (sExponent a b) = rExponent a b := by
  ext <;> rfl

@[simp] theorem reverseExponent_rBranch (a b i j k : ℕ) :
    reverseExponent (rBranch a b i j k) = sBranch a b i j k := by
  ext <;> rfl

@[simp] theorem reverseExponent_sBranch (a b i j k : ℕ) :
    reverseExponent (sBranch a b i j k) = rBranch a b i j k := by
  ext <;> rfl

/-- Reversal preserves the original balanced grading. -/
theorem balanced_reverseExponent
    {a b : ℕ} {u : Exponent} (h : Balanced a b u) :
    Balanced a b (reverseExponent u) := by
  change a * u.x4 + b * u.x3 = b * u.x2 + a * u.x1
  calc
    a * u.x4 + b * u.x3 = b * u.x3 + a * u.x4 := Nat.add_comm _ _
    _ = a * u.x1 + b * u.x2 := h.symm
    _ = b * u.x2 + a * u.x1 := Nat.add_comm _ _

@[simp] theorem balanced_reverseExponent_iff
    {a b : ℕ} {u : Exponent} :
    Balanced a b (reverseExponent u) ↔ Balanced a b u := by
  constructor
  · intro h
    have := balanced_reverseExponent h
    simpa using this
  · exact balanced_reverseExponent

/-- Reversal negates the secondary branch character. -/
@[simp] theorem branchCharacter_reverseExponent (u : Exponent) :
    branchCharacter (reverseExponent u) = -branchCharacter u := by
  change (u.x4 : ℤ) - (u.x1 : ℤ) = -((u.x1 : ℤ) - (u.x4 : ℤ))
  ring

/-- Image of a support under coordinate reversal. -/
def reverseSet (S : Set Exponent) : Set Exponent :=
  reverseExponent '' S

@[simp] theorem mem_reverseSet_iff
    {S : Set Exponent} {u : Exponent} :
    u ∈ reverseSet S ↔ reverseExponent u ∈ S := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hu
    exact ⟨reverseExponent u, hu, by simp⟩

@[simp] theorem reverseSet_involutive (S : Set Exponent) :
    reverseSet (reverseSet S) = S := by
  ext u
  simp

/-- Reversal sends a fixed `r` level to the corresponding `s` level. -/
theorem onRLevel_reverseSet
    {a b k : ℕ} {S : Set Exponent}
    (hR : OnRLevel a b k S) :
    OnSLevel a b k (reverseSet S) := by
  intro u hu
  rcases hu with ⟨v, hv, rfl⟩
  rcases hR v hv with ⟨i, j, hV⟩
  refine ⟨i, j, ?_⟩
  rw [hV, reverseExponent_rBranch]

/-- Reversal sends a fixed `s` level to the corresponding `r` level. -/
theorem onSLevel_reverseSet
    {a b k : ℕ} {S : Set Exponent}
    (hS : OnSLevel a b k S) :
    OnRLevel a b k (reverseSet S) := by
  intro u hu
  rcases hu with ⟨v, hv, rfl⟩
  rcases hS v hv with ⟨i, j, hV⟩
  refine ⟨i, j, ?_⟩
  rw [hV, reverseExponent_sBranch]

end HC4.Toric
