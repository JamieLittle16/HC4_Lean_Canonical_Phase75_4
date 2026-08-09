import HC4.Newton.TerminalNonnegativeWeights
import Mathlib.Tactic

/-!
# The two-zero terminal weight pattern

For a nonnegative non-scalar terminal conformal face the handwritten
nonnegative-face theorem separates the cases by the number of zero weights.

This module isolates the `k = 2` boundary in standard coordinates.  If
coordinates `0` and `1` have weight zero, determinant nondegeneracy gives a
global complement-matching permutation.  Its images of `0` and `1` are two
distinct coordinates of weight `d`.  Since `d > 0`, neither image can be
`0` or `1`; in four variables they are therefore exactly `2` and `3`.

Consequently the terminal weight is literally

    (0, 0, d, d).

No torus classification is used.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The standard two-zero terminal weight pattern `(0,0,d,d)`. -/
def standardTwoZeroTerminalWeight
    (d : ℤ) : Fin 4 -> ℤ
  | 0 => 0
  | 1 => 0
  | 2 => d
  | 3 => d

@[simp] theorem standardTwoZeroTerminalWeight_zero
    (d : ℤ) :
    standardTwoZeroTerminalWeight d 0 = 0 := rfl

@[simp] theorem standardTwoZeroTerminalWeight_one
    (d : ℤ) :
    standardTwoZeroTerminalWeight d 1 = 0 := rfl

@[simp] theorem standardTwoZeroTerminalWeight_two
    (d : ℤ) :
    standardTwoZeroTerminalWeight d 2 = d := rfl

@[simp] theorem standardTwoZeroTerminalWeight_three
    (d : ℤ) :
    standardTwoZeroTerminalWeight d 3 = d := rfl

/-- A complement matching with two standard zero coordinates and positive
degree forces the two remaining coordinates to have weight `d`. -/
theorem complementPermutation_two_standard_zeros
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    (hd : 0 < d)
    (hperm :
      HasTerminalComplementWeightPermutation lambda d)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0) :
    lambda 2 = d ∧ lambda 3 = d := by
  rcases hperm with ⟨π, hπ⟩
  let a : Fin 4 := π 0
  let b : Fin 4 := π 1
  have ha : lambda a = d := by
    dsimp [a]
    have h := hπ 0
    rw [h0] at h
    linarith
  have hb : lambda b = d := by
    dsimp [b]
    have h := hπ 1
    rw [h1] at h
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, h0] at ha
    linarith
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, h1] at ha
    linarith
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, h0] at hb
    linarith
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, h1] at hb
    linarith
  have hab : a ≠ b := by
    intro hab'
    have h01 : (0 : Fin 4) = 1 := by
      apply π.injective
      simpa [a, b] using hab'
    exact Fin.zero_ne_one h01

  have ha0v : a.val ≠ 0 := by
    intro hval
    apply ha0
    apply Fin.ext
    simpa using hval
  have ha1v : a.val ≠ 1 := by
    intro hval
    apply ha1
    apply Fin.ext
    simpa using hval
  have hb0v : b.val ≠ 0 := by
    intro hval
    apply hb0
    apply Fin.ext
    simpa using hval
  have hb1v : b.val ≠ 1 := by
    intro hval
    apply hb1
    apply Fin.ext
    simpa using hval

  have ha23v : a.val = 2 ∨ a.val = 3 := by
    omega
  have hb23v : b.val = 2 ∨ b.val = 3 := by
    omega

  have ha23 : a = (2 : Fin 4) ∨ a = (3 : Fin 4) := by
    rcases ha23v with ha2 | ha3
    · left
      apply Fin.ext
      exact ha2
    · right
      apply Fin.ext
      exact ha3
  have hb23 : b = (2 : Fin 4) ∨ b = (3 : Fin 4) := by
    rcases hb23v with hb2 | hb3
    · left
      apply Fin.ext
      exact hb2
    · right
      apply Fin.ext
      exact hb3

  rcases ha23 with ha2 | ha3
  · rcases hb23 with hb2 | hb3
    · exfalso
      apply hab
      calc
        a = (2 : Fin 4) := ha2
        _ = b := hb2.symm
    · constructor
      · simpa [ha2] using ha
      · simpa [hb3] using hb
  · rcases hb23 with hb2 | hb3
    · constructor
      · simpa [hb2] using hb
      · simpa [ha3] using ha
    · exfalso
      apply hab
      calc
        a = (3 : Fin 4) := ha3
        _ = b := hb3.symm

/-- In a nonnegative terminal conformal face, two standard zero weights
force the exact standard pattern `(0,0,d,d)`. -/
theorem nonnegativeTerminalFace_two_standard_zeros_weight_eq
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0) :
    lambda = standardTwoZeroTerminalWeight d := by
  have hd :
      0 < d :=
    nonnegative_nonScalar_terminal_degree_pos
      hface hnonneg
  have hperm :
      HasTerminalComplementWeightPermutation lambda d :=
    nonScalarTerminalConformalFace_has_complementWeightPermutation
      hface
  have h23 :
      lambda 2 = d ∧ lambda 3 = d :=
    complementPermutation_two_standard_zeros
      hd hperm h0 h1
  funext i
  fin_cases i <;>
    simp [standardTwoZeroTerminalWeight, h0, h1, h23.1, h23.2]

/-- The same two-zero hypotheses also record the positivity of the common
terminal degree, which will be used to cancel `d` in support equations. -/
theorem nonnegativeTerminalFace_two_standard_zeros_degree_pos
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (_h0 : lambda 0 = 0)
    (_h1 : lambda 1 = 0) :
    0 < d :=
  nonnegative_nonScalar_terminal_degree_pos
    hface hnonneg

end

end HC4.Newton
