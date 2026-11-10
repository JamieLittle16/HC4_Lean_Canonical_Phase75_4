import HC4.Valuation.QuadraticTransverseCapSourceHessianSchurDerivative
import Mathlib.Tactic

/-!
# Pivot-free rank-two obstruction from three source Schur derivative jets

The old seven-section endpoint required exact determinant-one equations
at the marked axis and six opposite transverse unit sections. The
actual source determinant-one identity can instead be differentiated
in each transverse direction. On a literal transverse quadratic source,
the transverse Hessian block is frozen in those directions.

After restricting to the marked axis, the derivative equations give
the THREE exact relations (C') * adj(C) * b' = 0. The remainder of the
rank-two endpoint is exactly the previously verified polynomial
unimodular kernel drift argument: differentiate Cw=0, obtain Cw'=0,
apply the universal adjugate kernel-line identity, and use the marked
endpoint collision.

There are no selected pivots, transverse shears, fractions, rank
localizations or section assumptions in this endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Genuine rank-two source-level impossibility from the marked-axis
unit Schur determinant and the three exact transverse derivative jets. -/
theorem quadraticTransverseCap_rankTwo_axisJet_impossible
    (C : GeneralThreeBlock (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (u : Polynomial K)
    (hthree : C.determinantCore = 0)
    (haxis :
      quadraticAxisFourBlockCore u
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1)
    (hjet₀ :
      Polynomial.derivative C.a * (quadraticTransverseAdjugateVector0 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.b * (quadraticTransverseAdjugateVector1 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.c * (quadraticTransverseAdjugateVector2 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) = 0)
    (hjet₁ :
      Polynomial.derivative C.b * (quadraticTransverseAdjugateVector0 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.d * (quadraticTransverseAdjugateVector1 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.e * (quadraticTransverseAdjugateVector2 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) = 0)
    (hjet₂ :
      Polynomial.derivative C.c * (quadraticTransverseAdjugateVector0 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.e * (quadraticTransverseAdjugateVector1 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) +
      Polynomial.derivative C.f * (quadraticTransverseAdjugateVector2 C (Polynomial.derivative (b 0)) (Polynomial.derivative (b 1)) (Polynomial.derivative (b 2))) = 0)
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
