import HC4.Valuation.QuadraticTransverseCapSourceRiccatiJets
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# Exact twice-differentiated Schur core for constant transverse blocks

This lemma extracts the quadratic transverse Hessian coefficient
without inventing a formal Taylor normal form.

Let H be the longitudinal Hessian entry, v the three mixed entries,
and C the symmetric transverse Hessian block. Let D and E be two
K-linear derivations. If C is constant under both derivations and
the mixed entries have vanishing mixed second derivative E(D(v)),
then directly differentiating the exact four-block Schur determinant
gives

  E(D(detCore)) = (det C) E(D H) -
                  2 (D v)^T adj(C) (E v).

The formula is valid over any commutative K-algebra, for any two
derivations D and E, with *no matrix inverse* or generic-rank
hypothesis. The source adapter takes D,E to the actual transverse
formal partial derivatives.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- A derivative annihilates all scalar 3x3 adjugate entries when
it annihilates the six independent transverse-block entries. -/
private theorem schur_derivative_adjugateVector
    (E : Derivation K R R)
    (C : GeneralThreeBlock R)
    (v₀ v₁ v₂ : R)
    (hzero :
      E C.a = 0 ∧ E C.b = 0 ∧ E C.c = 0 ∧
      E C.d = 0 ∧ E C.e = 0 ∧ E C.f = 0) :
    E (quadraticTransverseAdjugateVector0 C v₀ v₁ v₂) =
        quadraticTransverseAdjugateVector0 C
          (E v₀) (E v₁) (E v₂) ∧
    E (quadraticTransverseAdjugateVector1 C v₀ v₁ v₂) =
        quadraticTransverseAdjugateVector1 C
          (E v₀) (E v₁) (E v₂) ∧
    E (quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) =
        quadraticTransverseAdjugateVector2 C
          (E v₀) (E v₁) (E v₂) := by
  rcases hzero with ⟨ha, hb, hc, hd, he, hf⟩
  constructor
  · simp [quadraticTransverseAdjugateVector0, E.leibniz,
      ha, hb, hc, hd, he, hf, smul_eq_mul]
    ring
  constructor
  · simp [quadraticTransverseAdjugateVector1, E.leibniz,
      ha, hb, hc, hd, he, hf, smul_eq_mul]
    ring
  · simp [quadraticTransverseAdjugateVector2, E.leibniz,
      ha, hb, hc, hd, he, hf, smul_eq_mul]
    ring

/-- When the 3x3 block is constant in the chosen derivative,
the exact Schur first derivative is the determinant times
the longitudinal derivative minus twice the adjugate pairing
with the mixed derivative. -/
theorem quadraticTransverse_schur_firstDerivative
    (D : Derivation K R R)
    (H v₀ v₁ v₂ : R)
    (C : GeneralThreeBlock R)
    (hzero :
      D C.a = 0 ∧ D C.b = 0 ∧ D C.c = 0 ∧
      D C.d = 0 ∧ D C.e = 0 ∧ D C.f = 0) :
    D (quadraticAxisFourBlockCore H v₀ v₁ v₂
      C.a C.b C.c C.d C.e C.f) =
      D H * C.determinantCore -
      2 * (D v₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
           D v₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
           D v₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) := by
  rcases hzero with ⟨ha, hb, hc, hd, he, hf⟩
  simp [quadraticAxisFourBlockCore, GeneralThreeBlock.determinantCore,
    quadraticTransverseAdjugateVector0,
    quadraticTransverseAdjugateVector1,
    quadraticTransverseAdjugateVector2,
    D.leibniz, ha, hb, hc, hd, he, hf, smul_eq_mul]
  ring

/-- The general twice-differentiated Schur identity: the coefficient
tensor is a genuine adjugate quadratic form on the two mixed
Hessian derivative rows, and the longitudinal second jet. -/
theorem quadraticTransverse_schur_secondDerivative
    (D E : Derivation K R R)
    (H v₀ v₁ v₂ : R)
    (C : GeneralThreeBlock R)
    (hD :
      D C.a = 0 ∧ D C.b = 0 ∧ D C.c = 0 ∧
      D C.d = 0 ∧ D C.e = 0 ∧ D C.f = 0)
    (hE :
      E C.a = 0 ∧ E C.b = 0 ∧ E C.c = 0 ∧
      E C.d = 0 ∧ E C.e = 0 ∧ E C.f = 0)
    (hv₀ : E (D v₀) = 0)
    (hv₁ : E (D v₁) = 0)
    (hv₂ : E (D v₂) = 0) :
    E (D (quadraticAxisFourBlockCore H v₀ v₁ v₂
        C.a C.b C.c C.d C.e C.f)) =
      E (D H) * C.determinantCore -
      2 * (
        D v₀ * quadraticTransverseAdjugateVector0 C
          (E v₀) (E v₁) (E v₂) +
        D v₁ * quadraticTransverseAdjugateVector1 C
          (E v₀) (E v₁) (E v₂) +
        D v₂ * quadraticTransverseAdjugateVector2 C
          (E v₀) (E v₁) (E v₂)) := by
  have hfirst := quadraticTransverse_schur_firstDerivative
    D H v₀ v₁ v₂ C hD
  obtain ⟨hw₀, hw₁, hw₂⟩ :=
    schur_derivative_adjugateVector E C v₀ v₁ v₂ hE
  have hdet : E C.determinantCore = 0 := by
    rcases hE with ⟨ha, hb, hc, hd, he, hf⟩
    simp [GeneralThreeBlock.determinantCore, E.leibniz,
      ha, hb, hc, hd, he, hf, smul_eq_mul]
  calc
    E (D (quadraticAxisFourBlockCore H v₀ v₁ v₂
        C.a C.b C.c C.d C.e C.f)) =
      E (D H * C.determinantCore -
        2 * (D v₀ * quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
             D v₁ * quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
             D v₂ * quadraticTransverseAdjugateVector2 C v₀ v₁ v₂)) := by
               rw [hfirst]
    _ = E (D H) * C.determinantCore -
      2 * (
        D v₀ * quadraticTransverseAdjugateVector0 C
          (E v₀) (E v₁) (E v₂) +
        D v₁ * quadraticTransverseAdjugateVector1 C
          (E v₀) (E v₁) (E v₂) +
        D v₂ * quadraticTransverseAdjugateVector2 C
          (E v₀) (E v₁) (E v₂)) := by
               simp [E.leibniz, hdet, hw₀, hw₁, hw₂,
                 hv₀, hv₁, hv₂, smul_eq_mul]
               ring

end

end HC4.Valuation
