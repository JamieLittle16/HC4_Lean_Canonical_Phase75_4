import HC4.Valuation.QuadraticTransverseCapThreePrincipalKernel
import HC4.Valuation.QuadraticTransverseCapSingularPrincipalPivot
import HC4.Valuation.QuadraticTransverseCapSchurOddCancellation
import Mathlib.Tactic

/-!
# The seven-section quadratic rank-two Schur endpoint

The original five-section endpoint used the (0,1) principal pivot.
The real represented source only guarantees one of three principal
pivots, but supplies determinant one at ALL constant transverse
sections.

Here the three opposite pairs y=±e_j (j=0,1,2) give ALL rows
of C'(x)w=0, for w=adj(C)b'. The axis equation gives Cw=0
and w·b'=-1; differentiating gives Cw'=0. Then ANY principal
2x2 pivot implies w∧w'=0, and unimodularity plus the original
marked collision gives a contradiction.

The only remaining source-level obligations are to identify the
actual Hessian sections as v±C'e_j with fixed C and to invoke
their already-proved source determinant-one equations.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- All three opposite transverse pairs eliminate the need to
distinguish which original principal 2x2 minor is nonzero.

The `hplus` and `hminus` hypotheses are six *explicit scalar
determinant equations*; they are not a prepackaged rank-two
contradiction or new endpoint producer. -/
theorem quadraticTransverseCap_rankTwo_sevenSchurSections_impossible
    (C : GeneralThreeBlock (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (u : Polynomial K)
    (up um : Fin 3 → Polynomial K)
    (hthree : C.determinantCore = 0)
    (hpivot :
      C.d * C.f - C.e * C.e ≠ 0 ∨
      C.a * C.f - C.c * C.c ≠ 0 ∨
      C.a * C.d - C.b * C.b ≠ 0)
    (haxis :
      quadraticAxisFourBlockCore u
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1)
    (hplus : ∀ j : Fin 3,
      quadraticAxisFourBlockCore (up j)
        (Polynomial.derivative (b 0) +
          Polynomial.derivative (C.matrix 0 j))
        (Polynomial.derivative (b 1) +
          Polynomial.derivative (C.matrix 1 j))
        (Polynomial.derivative (b 2) +
          Polynomial.derivative (C.matrix 2 j))
        C.a C.b C.c C.d C.e C.f = 1)
    (hminus : ∀ j : Fin 3,
      quadraticAxisFourBlockCore (um j)
        (Polynomial.derivative (b 0) -
          Polynomial.derivative (C.matrix 0 j))
        (Polynomial.derivative (b 1) -
          Polynomial.derivative (C.matrix 1 j))
        (Polynomial.derivative (b 2) -
          Polynomial.derivative (C.matrix 2 j))
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
  have hjet (j : Fin 3) :
      Polynomial.derivative (C.matrix 0 j) * w₀ +
        Polynomial.derivative (C.matrix 1 j) * w₁ +
        Polynomial.derivative (C.matrix 2 j) * w₂ = 0 := by
    exact quadraticAxisFourBlockCore_oddPairing_zero_of_unit
      (up j) (um j) v₀ v₁ v₂
      (Polynomial.derivative (C.matrix 0 j))
      (Polynomial.derivative (C.matrix 1 j))
      (Polynomial.derivative (C.matrix 2 j))
      C hthree (hplus j) (hminus j)
  have hjet₀ :
      Polynomial.derivative C.a * w₀ +
        Polynomial.derivative C.b * w₁ +
        Polynomial.derivative C.c * w₂ = 0 := by
    simpa [GeneralThreeBlock.matrix] using hjet (0 : Fin 3)
  have hjet₁ :
      Polynomial.derivative C.b * w₀ +
        Polynomial.derivative C.d * w₁ +
        Polynomial.derivative C.e * w₂ = 0 := by
    simpa [GeneralThreeBlock.matrix] using hjet (1 : Fin 3)
  have hjet₂ :
      Polynomial.derivative C.c * w₀ +
        Polynomial.derivative C.e * w₁ +
        Polynomial.derivative C.f * w₂ = 0 := by
    simpa [GeneralThreeBlock.matrix] using hjet (2 : Fin 3)
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
  have hpair :
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) = -1 := by
    calc
      (∑ i : Fin 3, w i * Polynomial.derivative (b i)) =
        w₀ * v₀ + w₁ * v₁ + w₂ * v₂ := by
          simp [Fin.sum_univ_three, w, v₀, v₁, v₂]
      _ = -1 := by
          linear_combination hpair₀
  obtain ⟨h01, h02, h12⟩ :=
    quadraticTransverse_threePrincipalKernel_wedges C
      w (fun i => Polynomial.derivative (w i))
      hpivot
      (by simpa [w] using hker₀)
      (by simpa [w] using hker₁)
      (by simpa [w] using hker₂)
      (by simpa [w] using hder₀)
      (by simpa [w] using hder₁)
      (by simpa [w] using hder₂)
  have hwedge : ∀ i j : Fin 3,
      w i * Polynomial.derivative (w j) =
        w j * Polynomial.derivative (w i) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact sub_eq_zero.mp h01
      | exact sub_eq_zero.mp h02
      | exact sub_eq_zero.mp h12
      | exact (sub_eq_zero.mp h01).symm
      | exact (sub_eq_zero.mp h02).symm
      | exact (sub_eq_zero.mp h12).symm
  exact polynomial_unimodularKernel_markedDrift_impossible
    w b hpair hwedge hcoll

end

end HC4.Valuation
