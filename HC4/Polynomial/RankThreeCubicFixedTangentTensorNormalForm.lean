import HC4.Polynomial.RankThreeCubicFixedTangentNormalForm
import Mathlib.Tactic

/-!
# Source-compatible cubic tensor: a fixed tangent kernel determines normal form

The five-parameter matrix in FixedTangentNormalForm is not an
unrelated model. Any fully symmetric ternary cubic tensor D whose
Hessian at (0,u,v) kills e_v must have exactly this form, with
parameters D000, D001, D002, D011, D111.

All identities are over the original base field, and no
determinant factorisation or scalar triple-pole assumption
is used. This lemma will be transported through the
pole-adapted frame after e_v is chosen as the fixed kernel.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 2500000

theorem cubicTensor_fixedTangentKernel_exactFiveParameterForm
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hfixed : ∀ u v : K,
      let H := cubicTensorHessianAt D ![(0 : K), u, v]
      H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0)
    (z u v : K) :
    cubicTensorHessianAt D ![z,u,v] =
      cubicFixedTangentHessian
        (D 0 0 0) (D 0 0 1) (D 0 0 2)
        (D 0 1 1) (D 1 1 1) z u v := by
  classical
  have h102 : D 1 0 2 = 0 := by
    have h := (hfixed 1 0).1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h202 : D 2 0 2 = 0 := by
    have h := (hfixed 0 1).1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h112 : D 1 1 2 = 0 := by
    have h := (hfixed 1 0).2.1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h212 : D 2 1 2 = 0 := by
    have h := (hfixed 0 1).2.1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h122 : D 1 2 2 = 0 := by
    have h := (hfixed 1 0).2.2
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h222 : D 2 2 2 = 0 := by
    have h := (hfixed 0 1).2.2
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h010 : D 0 1 0 = D 0 0 1 := hswap₂ 0 1 0
  have h020 : D 0 2 0 = D 0 0 2 := hswap₂ 0 2 0
  have h100 : D 1 0 0 = D 0 0 1 :=
    (hswap₁ 1 0 0).trans (hswap₂ 0 1 0)
  have h200 : D 2 0 0 = D 0 0 2 :=
    (hswap₁ 2 0 0).trans (hswap₂ 0 2 0)
  have h101 : D 1 0 1 = D 0 1 1 := hswap₁ 1 0 1
  have h110 : D 1 1 0 = D 0 1 1 :=
    (hswap₂ 1 1 0).trans (hswap₁ 1 0 1)
  have h012 : D 0 1 2 = 0 := (hswap₁ 0 1 2).trans h102
  have h021 : D 0 2 1 = 0 := (hswap₂ 0 2 1).trans h012
  have h120 : D 1 2 0 = 0 := (hswap₂ 1 2 0).trans h102
  have h201 : D 2 0 1 = 0 := (hswap₁ 2 0 1).trans h021
  have h210 : D 2 1 0 = 0 := (hswap₂ 2 1 0).trans h201
  have h211 : D 2 1 1 = 0 := by
    rw [hswap₁ 2 1 1, hswap₂ 1 2 1]
    exact h112
  have h121 : D 1 2 1 = 0 := (hswap₂ 1 2 1).trans h112
  have h221 : D 2 2 1 = 0 := (hswap₂ 2 2 1).trans h212
  have h220 : D 2 2 0 = 0 := (hswap₂ 2 2 0).trans h202
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicTensorHessianAt, cubicFixedTangentHessian,
      Fin.sum_univ_three, h102, h202, h112, h212, h122, h222,
      h010, h020, h100, h200, h101, h110, h012, h021,
      h120, h201, h210, h211, h121, h221, h220] <;> ring

end
end HC4.Polynomial.RankThreeCubic
