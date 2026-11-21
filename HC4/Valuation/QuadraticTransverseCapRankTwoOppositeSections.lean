import HC4.Valuation.QuadraticTransverseCapTwoRowKernel
import HC4.Valuation.QuadraticTransverseCapSchurOddCancellation
import Mathlib.Tactic

/-!
# Rank-two transverse quadratic endpoint from five actual Schur identities

For transverse cap two, let C(x) denote the symmetric 3x3 transverse
Hessian on the marked axis, and v(x)=b'(x). At y=0 and at the four
sections y=±e₁, ±e₂ the determinant-one condition gives five exact
four-block scalar Schur equations. Each pair of opposite sections
has the same C and mixed Hessian columns v±C' eᵢ; the longitudinal
entry can be different at the two sections.

In the det(C)=0 branch, the axis Schur equation constructs the
unimodular polynomial kernel w=adj(C)v. The two opposite-section
pairs give the first two rows of C'w=0. Differentiating Cw=0
then gives Cw'=0. A genuine principal 2x2 pivot and the original
marked collision make this impossible.

This theorem has no hypothesis of the shape 'kernel derivative
vanishes' or 'final producer exists'. Its open *source adapter*
obligations are solely the five honest determinant evaluations,
the principal pivot (possibly after source shear), and the
source transverse coefficient definitions.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Rank-two represented transverse Schur endpoint with unit determinant
on the axis and the two opposite coordinate-pair sections. -/
theorem quadraticTransverseCap_rankTwo_oppositeSections_impossible
    (C : GeneralThreeBlock (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (u up₀ um₀ up₁ um₁ : Polynomial K)
    (hthree : C.determinantCore = 0)
    (hpivot : C.a * C.d - C.b * C.b ≠ 0)
    (haxis :
      quadraticAxisFourBlockCore u
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1)
    (hplus₀ :
      quadraticAxisFourBlockCore up₀
        (Polynomial.derivative (b 0) + Polynomial.derivative C.a)
        (Polynomial.derivative (b 1) + Polynomial.derivative C.b)
        (Polynomial.derivative (b 2) + Polynomial.derivative C.c)
        C.a C.b C.c C.d C.e C.f = 1)
    (hminus₀ :
      quadraticAxisFourBlockCore um₀
        (Polynomial.derivative (b 0) - Polynomial.derivative C.a)
        (Polynomial.derivative (b 1) - Polynomial.derivative C.b)
        (Polynomial.derivative (b 2) - Polynomial.derivative C.c)
        C.a C.b C.c C.d C.e C.f = 1)
    (hplus₁ :
      quadraticAxisFourBlockCore up₁
        (Polynomial.derivative (b 0) + Polynomial.derivative C.b)
        (Polynomial.derivative (b 1) + Polynomial.derivative C.d)
        (Polynomial.derivative (b 2) + Polynomial.derivative C.e)
        C.a C.b C.c C.d C.e C.f = 1)
    (hminus₁ :
      quadraticAxisFourBlockCore um₁
        (Polynomial.derivative (b 0) - Polynomial.derivative C.b)
        (Polynomial.derivative (b 1) - Polynomial.derivative C.d)
        (Polynomial.derivative (b 2) - Polynomial.derivative C.e)
        C.a C.b C.c C.d C.e C.f = 1)
    (hcoll : ∀ i : Fin 3,
      Polynomial.eval (1 : K) (b i) =
        Polynomial.eval (0 : K) (b i)) :
    False := by
  let v₀ := Polynomial.derivative (b 0)
  let v₁ := Polynomial.derivative (b 1)
  let v₂ := Polynomial.derivative (b 2)
  let w₀ := quadraticTransverseAdjugateVector0 C v₀ v₁ v₂
  let w₁ := quadraticTransverseAdjugateVector1 C v₀ v₁ v₂
  let w₂ := quadraticTransverseAdjugateVector2 C v₀ v₁ v₂
  let w : Fin 3 → Polynomial K := ![w₀, w₁, w₂]
  have hcert :=
    quadraticTransverse_singularThreeBlock_unimodularKernel
      u v₀ v₁ v₂ C haxis hthree
  dsimp only at hcert
  obtain ⟨hpair₀, hker₀, hker₁, _⟩ := hcert
  have hjet₀ :
      Polynomial.derivative C.a * w₀ +
      Polynomial.derivative C.b * w₁ +
      Polynomial.derivative C.c * w₂ = 0 := by
    exact quadraticAxisFourBlockCore_oddPairing_zero_of_unit
      up₀ um₀ v₀ v₁ v₂
      (Polynomial.derivative C.a)
      (Polynomial.derivative C.b)
      (Polynomial.derivative C.c)
      C hthree hplus₀ hminus₀
  have hjet₁ :
      Polynomial.derivative C.b * w₀ +
      Polynomial.derivative C.d * w₁ +
      Polynomial.derivative C.e * w₂ = 0 := by
    exact quadraticAxisFourBlockCore_oddPairing_zero_of_unit
      up₁ um₁ v₀ v₁ v₂
      (Polynomial.derivative C.b)
      (Polynomial.derivative C.d)
      (Polynomial.derivative C.e)
      C hthree hplus₁ hminus₁
  have hder₀ :
      C.a * Polynomial.derivative w₀ +
      C.b * Polynomial.derivative w₁ +
      C.c * Polynomial.derivative w₂ = 0 := by
    have hd := congrArg Polynomial.derivative hker₀
    simp only [map_add, Polynomial.derivative_mul,
      Polynomial.derivative_zero] at hd
    linear_combination hd - hjet₀
  have hder₁ :
      C.b * Polynomial.derivative w₀ +
      C.d * Polynomial.derivative w₁ +
      C.e * Polynomial.derivative w₂ = 0 := by
    have hd := congrArg Polynomial.derivative hker₁
    simp only [map_add, Polynomial.derivative_mul,
      Polynomial.derivative_zero] at hd
    linear_combination hd - hjet₁
  have hpair :
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) = -1 := by
    calc
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) =
        w₀ * v₀ + w₁ * v₁ + w₂ * v₂ := by
          simp [Fin.sum_univ_three, w, v₀, v₁, v₂]
      _ = -1 := by
          linear_combination hpair₀
  exact quadraticTransverseCap_rankTwo_principalKernelCollision_impossible
    C.a C.b C.c C.d C.e w b hpivot
    (by simpa [w] using hker₀)
    (by simpa [w] using hker₁)
    (by simpa [w] using hder₀)
    (by simpa [w] using hder₁)
    hpair hcoll

end

end HC4.Valuation
