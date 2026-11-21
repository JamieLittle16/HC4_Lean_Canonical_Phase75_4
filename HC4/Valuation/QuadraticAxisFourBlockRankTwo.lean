import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# A quadratic-axis determinant forces a transverse rank-two minor

An exact symmetric 4x4 polynomial-parameter Hessian pencil whose longitudinal
diagonal is order two, whose longitudinal-transverse entries are order one,
and whose transverse block is parameter-independent has determinant

  tau^2 * (a det(C) - b^T adj(C) b).

Here the factor in parentheses is expressed directly in the six independent
2x2 minors of the transverse symmetric 3x3 matrix.  If the determinant is
exactly tau^2 and tau is nonzero in a domain, one of those minors MUST be
nonzero.  No Hessian family or source-reentry hypothesis is used in this
pure commutative-ring lemma; a separate geometric adapter must prove that
a concrete E3 quadratic family has this particular origin-Hessian profile.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {R : Type u} [CommRing R]

/-- Symmetric origin-Hessian pencil with a parameter-independent transverse
three-block and longitudinal row of valuation at least one. -/
def quadraticAxisFourBlock
    (t a b c d e f g h i j : R) : GeneralFourBlock R where
  a := t ^ 2 * a
  b := t * b
  d := e
  p := t * c
  q := t * d
  r := f
  s := g
  x := h
  y := i
  z := j

/-- The scalar factor of the quadratic-axis Hessian determinant, written
only in terms of the six independent transverse 2x2 minors. -/
def quadraticAxisFourBlockCore
    (a b c d e f g h i j : R) : R :=
  a * (e * (h * j - i * i) -
       f * (f * j - g * i) +
       g * (f * i - g * h)) -
  b * b * (h * j - i * i) +
  2 * b * c * (f * j - g * i) -
  2 * b * d * (f * i - g * h) -
  c * c * (e * j - g * g) +
  2 * c * d * (e * i - f * g) -
  d * d * (e * h - f * f)

/-- Exact determinant factorisation, valid over *any* commutative ring. -/
theorem quadraticAxisFourBlock_determinantCore
    (t a b c d e f g h i j : R) :
    (quadraticAxisFourBlock t a b c d e f g h i j).determinantCore =
      t ^ 2 * quadraticAxisFourBlockCore a b c d e f g h i j := by
  dsimp [quadraticAxisFourBlock, quadraticAxisFourBlockCore,
    GeneralFourBlock.determinantCore]
  ring

/-- Nonzero unit quadratic clock forces an actual nonzero 2x2 minor on
the constant transverse three-block.  This is the rank-two witness,
not merely a nonzero matrix entry or a formal repair label. -/
theorem quadraticAxisFourBlock_exists_transverseMinor
    [IsDomain R]
    (t a b c d e f g h i j : R)
    (ht : t ≠ 0)
    (hdet :
      (quadraticAxisFourBlock t a b c d e f g h i j).determinantCore =
        t ^ 2) :
    h * j - i * i ≠ 0 ∨
    f * j - g * i ≠ 0 ∨
    f * i - g * h ≠ 0 ∨
    e * j - g * g ≠ 0 ∨
    e * i - f * g ≠ 0 ∨
    e * h - f * f ≠ 0 := by
  have hfactor :=
    quadraticAxisFourBlock_determinantCore t a b c d e f g h i j
  rw [hdet] at hfactor
  have hcore :
      quadraticAxisFourBlockCore a b c d e f g h i j = 1 := by
    have hmul :
        t ^ 2 * quadraticAxisFourBlockCore a b c d e f g h i j =
          t ^ 2 * 1 := by
      simpa using hfactor.symm
    exact mul_left_cancel₀ (pow_ne_zero 2 ht) hmul
  by_contra hnone
  simp only [not_or, not_not] at hnone
  rcases hnone with ⟨h1, h2, h3, h4, h5, h6⟩
  have hzero :
      quadraticAxisFourBlockCore a b c d e f g h i j = 0 := by
    dsimp [quadraticAxisFourBlockCore]
    rw [h1, h2, h3, h4, h5, h6]
    ring
  exact one_ne_zero (hcore.symm.trans hzero)

end

end HC4.Valuation
