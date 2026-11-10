import HC4.Valuation.QuadraticTransverseCapSchurOddCancellation
import HC4.Valuation.QuadraticTransverseCapRankTwoKernelDrift
import Mathlib.Tactic

/-!
# Pivot-free adjugate kernel endpoint for transverse-quadratic sources

For symmetric C, w = adj(C)v and Cz=0 imply
  w_i (v.z) = z_i (v.w)  for i=0,1,2,
over any commutative ring. No generic-rank argument, chosen pivot,
transverse shear or fraction-field localization is required.

When det(C)=0 and the whole Hessian determinant is one, v.w=-1.
The odd parts of the seven determinant-one sections (the axis and
the positive and negative transverse basis sections) give C'w=0. Differentiating Cw=0
gives Cw'=0, so the adjugate identity with z=w' forces the polynomial
kernel vector's derivative wedges to vanish. The existing polynomial
unimodular-kernel drift theorem then contradicts the marked collision.

The seven section identities and collision must still be extracted from
the actual represented source; this does not close E3 on its own.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

universe u
variable {R : Type u} [CommRing R]

/-- Symmetric three-block adjugate kernel-line identity. The three
kernel row equations are sufficient even over a non-domain ring. -/
theorem quadraticTransverse_adjugateKernel_line
    (C : GeneralThreeBlock R)
    (v₀ v₁ v₂ z₀ z₁ z₂ : R)
    (hz₀ : C.a * z₀ + C.b * z₁ + C.c * z₂ = 0)
    (hz₁ : C.b * z₀ + C.d * z₁ + C.e * z₂ = 0)
    (hz₂ : C.c * z₀ + C.e * z₁ + C.f * z₂ = 0) :
    let w₀ := quadraticTransverseAdjugateVector0 C v₀ v₁ v₂
    let w₁ := quadraticTransverseAdjugateVector1 C v₀ v₁ v₂
    let w₂ := quadraticTransverseAdjugateVector2 C v₀ v₁ v₂
    w₀ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) =
      z₀ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) ∧
    w₁ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) =
      z₁ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) ∧
    w₂ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) =
      z₂ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) := by
  let w₀ := quadraticTransverseAdjugateVector0 C v₀ v₁ v₂
  let w₁ := quadraticTransverseAdjugateVector1 C v₀ v₁ v₂
  let w₂ := quadraticTransverseAdjugateVector2 C v₀ v₁ v₂
  let s₀₀ : R := -C.d * v₂ * v₂ + 2 * C.e * v₁ * v₂ - C.f * v₁ * v₁
  let s₀₁ : R := C.b * v₂ * v₂ - C.c * v₁ * v₂ - C.e * v₀ * v₂ + C.f * v₀ * v₁
  let s₀₂ : R := -C.b * v₁ * v₂ + C.c * v₁ * v₁ + C.d * v₀ * v₂ - C.e * v₀ * v₁
  let s₁₁ : R := -C.a * v₂ * v₂ + 2 * C.c * v₀ * v₂ - C.f * v₀ * v₀
  let s₁₂ : R := C.a * v₁ * v₂ - C.b * v₀ * v₂ - C.c * v₀ * v₁ + C.e * v₀ * v₀
  let s₂₂ : R := -C.a * v₁ * v₁ + 2 * C.b * v₀ * v₁ - C.d * v₀ * v₀
  have hid₀ :
      w₀ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) -
        z₀ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) =
      s₀₀ * (C.a * z₀ + C.b * z₁ + C.c * z₂) +
        s₀₁ * (C.b * z₀ + C.d * z₁ + C.e * z₂) +
        s₀₂ * (C.c * z₀ + C.e * z₁ + C.f * z₂) := by
    dsimp [w₀, w₁, w₂, s₀₀, s₀₁, s₀₂,
      quadraticTransverseAdjugateVector0,
      quadraticTransverseAdjugateVector1,
      quadraticTransverseAdjugateVector2]
    ring
  have hid₁ :
      w₁ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) -
        z₁ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) =
      s₀₁ * (C.a * z₀ + C.b * z₁ + C.c * z₂) +
        s₁₁ * (C.b * z₀ + C.d * z₁ + C.e * z₂) +
        s₁₂ * (C.c * z₀ + C.e * z₁ + C.f * z₂) := by
    dsimp [w₀, w₁, w₂, s₀₁, s₁₁, s₁₂,
      quadraticTransverseAdjugateVector0,
      quadraticTransverseAdjugateVector1,
      quadraticTransverseAdjugateVector2]
    ring
  have hid₂ :
      w₂ * (v₀ * z₀ + v₁ * z₁ + v₂ * z₂) -
        z₂ * (v₀ * w₀ + v₁ * w₁ + v₂ * w₂) =
      s₀₂ * (C.a * z₀ + C.b * z₁ + C.c * z₂) +
        s₁₂ * (C.b * z₀ + C.d * z₁ + C.e * z₂) +
        s₂₂ * (C.c * z₀ + C.e * z₁ + C.f * z₂) := by
    dsimp [w₀, w₁, w₂, s₀₂, s₁₂, s₂₂,
      quadraticTransverseAdjugateVector0,
      quadraticTransverseAdjugateVector1,
      quadraticTransverseAdjugateVector2]
    ring
  dsimp only
  refine ⟨sub_eq_zero.mp ?_, sub_eq_zero.mp ?_, sub_eq_zero.mp ?_⟩
  · rw [hid₀, hz₀, hz₁, hz₂]
    ring
  · rw [hid₁, hz₀, hz₁, hz₂]
    ring
  · rw [hid₂, hz₀, hz₁, hz₂]
    ring

variable {K : Type*} [Field K] [CharZero K]

/-- Rank-two source-level collision contradiction without any principal
pivot hypothesis. Seven source section equations suffice. -/
theorem quadraticTransverseCap_rankTwo_sevenSections_impossible
    (C : GeneralThreeBlock (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (u up₀ um₀ up₁ um₁ up₂ um₂ : Polynomial K)
    (hthree : C.determinantCore = 0)
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
    (hplus₂ :
      quadraticAxisFourBlockCore up₂
        (Polynomial.derivative (b 0) + Polynomial.derivative C.c)
        (Polynomial.derivative (b 1) + Polynomial.derivative C.e)
        (Polynomial.derivative (b 2) + Polynomial.derivative C.f)
        C.a C.b C.c C.d C.e C.f = 1)
    (hminus₂ :
      quadraticAxisFourBlockCore um₂
        (Polynomial.derivative (b 0) - Polynomial.derivative C.c)
        (Polynomial.derivative (b 1) - Polynomial.derivative C.e)
        (Polynomial.derivative (b 2) - Polynomial.derivative C.f)
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
  obtain ⟨hpair₀, hker₀, hker₁, hker₂⟩ := hcert
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
  have hjet₂ :
      Polynomial.derivative C.c * w₀ +
      Polynomial.derivative C.e * w₁ +
      Polynomial.derivative C.f * w₂ = 0 := by
    exact quadraticAxisFourBlockCore_oddPairing_zero_of_unit
      up₂ um₂ v₀ v₁ v₂
      (Polynomial.derivative C.c)
      (Polynomial.derivative C.e)
      (Polynomial.derivative C.f)
      C hthree hplus₂ hminus₂
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
  have hder₂ :
      C.c * Polynomial.derivative w₀ +
      C.e * Polynomial.derivative w₁ +
      C.f * Polynomial.derivative w₂ = 0 := by
    have hd := congrArg Polynomial.derivative hker₂
    simp only [map_add, Polynomial.derivative_mul,
      Polynomial.derivative_zero] at hd
    linear_combination hd - hjet₂
  have hline := quadraticTransverse_adjugateKernel_line
    C v₀ v₁ v₂
    (Polynomial.derivative w₀)
    (Polynomial.derivative w₁)
    (Polynomial.derivative w₂)
    hder₀ hder₁ hder₂
  dsimp only at hline
  obtain ⟨hl₀, hl₁, hl₂⟩ := hline
  rw [hpair₀] at hl₀ hl₁ hl₂
  have hwedge₀₁ :
      w₀ * Polynomial.derivative w₁ =
        w₁ * Polynomial.derivative w₀ := by
    linear_combination w₀ * hl₁ - w₁ * hl₀
  have hwedge₀₂ :
      w₀ * Polynomial.derivative w₂ =
        w₂ * Polynomial.derivative w₀ := by
    linear_combination w₀ * hl₂ - w₂ * hl₀
  have hwedge₁₂ :
      w₁ * Polynomial.derivative w₂ =
        w₂ * Polynomial.derivative w₁ := by
    linear_combination w₁ * hl₂ - w₂ * hl₁
  have hwedge : ∀ i j : Fin 3,
      w i * Polynomial.derivative (w j) =
        w j * Polynomial.derivative (w i) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact hwedge₀₁
      | exact hwedge₀₂
      | exact hwedge₁₂
      | exact hwedge₀₁.symm
      | exact hwedge₀₂.symm
      | exact hwedge₁₂.symm
  have hpair :
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) = -1 := by
    calc
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) =
          w₀ * v₀ + w₁ * v₁ + w₂ * v₂ := by
            simp [Fin.sum_univ_three, w, v₀, v₁, v₂]
      _ = -1 := by
          linear_combination hpair₀
  exact polynomial_unimodularKernel_markedDrift_impossible
    w b hpair hwedge hcoll

end
end HC4.Valuation
