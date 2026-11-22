import HC4.Polynomial.RankThreeCubicTensorFrameBinaryKernel
import HC4.Polynomial.RankThreeCubicZeroBinaryDeterminant
import Mathlib.Tactic

/-!
# A symmetric cubic tensor with zero binary Hessian: exact six-parameter normal form

When the lower-right tangential 2x2 block of the cubic Hessian
vanishes for all points (0,u,v), full symmetry of the cubic
tensor reduces it to six coefficients:
  alpha = D(0,0,0), beta = D(0,0,1), gamma = D(0,0,2),
  m = D(0,1,1), n = D(0,1,2), l = D(0,2,2).

The entire Hessian at (z,u,v) is the explicit
cubicZeroBinaryHessian alpha beta gamma m n l z u v.
This is an algebraic identity over a field, not an assumed
source normal form; it will be invoked only after deriving
the tensor and its zero binary block from the actual source.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- Exact normal form of a symmetric ternary cubic tensor whose
binary Hessian block vanishes identically on the plane z=0. -/
theorem cubicTensor_zeroBinaryBlock_exactNormalForm
    {K : Type*} [Field K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hzero : ∀ u v : K,
      let H := cubicTensorHessianAt D ![(0 : K), u, v]
      H 1 1 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0)
    (z u v : K) :
    cubicTensorHessianAt D ![z, u, v] =
      cubicZeroBinaryHessian
        (D 0 0 0) (D 0 0 1) (D 0 0 2)
        (D 0 1 1) (D 0 1 2) (D 0 2 2)
        z u v := by
  classical
  have h111 : D 1 1 1 = 0 := by
    have h := (hzero 1 0).1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h112 : D 1 1 2 = 0 := by
    have h := (hzero 1 0).2.1
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h122 : D 1 2 2 = 0 := by
    have h := (hzero 1 0).2.2
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h222 : D 2 2 2 = 0 := by
    have h := (hzero 0 1).2.2
    simpa [cubicTensorHessianAt, Fin.sum_univ_three] using h
  have h100 : D 1 0 0 = D 0 0 1 := by
    exact (hswap₁ 1 0 0).trans (hswap₂ 0 1 0)
  have h200 : D 2 0 0 = D 0 0 2 := by
    exact (hswap₁ 2 0 0).trans (hswap₂ 0 2 0)
  have h101 : D 1 0 1 = D 0 1 1 := hswap₁ 1 0 1
  have h201 : D 2 0 1 = D 0 1 2 := by
    exact (hswap₁ 2 0 1).trans (hswap₂ 0 2 1)
  have h102 : D 1 0 2 = D 0 1 2 := hswap₁ 1 0 2
  have h202 : D 2 0 2 = D 0 2 2 := hswap₁ 2 0 2
  have h110 : D 1 1 0 = D 0 1 1 := by
    exact (hswap₂ 1 1 0).trans (hswap₁ 1 0 1)
  have h210 : D 2 1 0 = D 0 1 2 := by
    exact (hswap₂ 2 1 0).trans h201
  have h211 : D 2 1 1 = 0 := by
    rw [hswap₁ 2 1 1, hswap₂ 1 2 1]
    exact h112
  have h212 : D 2 1 2 = 0 := by
    rw [hswap₁ 2 1 2]
    exact h122
  have h120 : D 1 2 0 = D 0 1 2 := by
    exact (hswap₂ 1 2 0).trans h102
  have h220 : D 2 2 0 = D 0 2 2 := by
    exact (hswap₂ 2 2 0).trans h202
  have h121 : D 1 2 1 = 0 := by
    rw [hswap₂ 1 2 1]
    exact h112
  have h221 : D 2 2 1 = 0 := by
    rw [hswap₂ 2 2 1, hswap₁ 2 1 2]
    exact h122
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicTensorHessianAt, cubicZeroBinaryHessian,
      Fin.sum_univ_three, h111, h112, h122, h222,
      h100, h200, h101, h201, h102, h202,
      h110, h210, h211, h212, h120, h220,
      h121, h221] <;> ring

/-- The zero binary block forces an exact scalar triple-normal
determinant whenever the determinant is known to have a
square-normal times linear factor. -/
theorem cubicTensor_zeroBinaryBlock_squareFactor_forces_tripleDet
    {K : Type*} [Field K] [CharZero K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hzero : ∀ u v : K,
      let H := cubicTensorHessianAt D ![(0 : K), u, v]
      H 1 1 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0)
    (A B C : K)
    (hfactor : ∀ z u v : K,
      (cubicTensorHessianAt D ![z, u, v]).det =
        z ^ 2 * (A * z + B * u + C * v)) :
    ∃ lambda : K,
      ∀ z u v : K,
        (cubicTensorHessianAt D ![z, u, v]).det =
          lambda * z ^ 3 := by
  let alpha := D 0 0 0
  let beta := D 0 0 1
  let gamma := D 0 0 2
  let m := D 0 1 1
  let n := D 0 1 2
  let l := D 0 2 2
  have hfac : ∀ z u v : K,
      (cubicZeroBinaryHessian alpha beta gamma m n l z u v).det =
        z ^ 2 * (A * z + B * u + C * v) := by
    intro z u v
    rw [← cubicTensor_zeroBinaryBlock_exactNormalForm
      D hswap₁ hswap₂ hzero z u v]
    exact hfactor z u v
  have hdisc : m * l = n ^ 2 :=
    cubicZeroBinaryHessian_discriminant_zero_of_squareNormalFactor
      alpha beta gamma m n l A B C hfac
  refine ⟨-beta ^ 2 * l + 2 * beta * gamma * n - gamma ^ 2 * m, ?_⟩
  intro z u v
  rw [cubicTensor_zeroBinaryBlock_exactNormalForm
    D hswap₁ hswap₂ hzero z u v]
  rw [cubicZeroBinaryHessian_det_triple_of_discriminant_zero
    alpha beta gamma m n l z u v hdisc]
  ring


/-- In the same situation, a putative square-normal times
linear factor must have *no tangential terms*. This is the
coefficient form best suited to proving p divides the source
complementary linear factor after returning from the frame. -/
theorem cubicTensor_zeroBinaryBlock_squareFactor_tangentCoefficients_zero
    {K : Type*} [Field K] [CharZero K]
    (D : Fin 3 → Fin 3 → Fin 3 → K)
    (hswap₁ : ∀ i j k : Fin 3, D i j k = D j i k)
    (hswap₂ : ∀ i j k : Fin 3, D i j k = D i k j)
    (hzero : ∀ u v : K,
      let H := cubicTensorHessianAt D ![(0 : K), u, v]
      H 1 1 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0)
    (A B C : K)
    (hfactor : ∀ z u v : K,
      (cubicTensorHessianAt D ![z, u, v]).det =
        z ^ 2 * (A * z + B * u + C * v)) :
    B = 0 ∧ C = 0 := by
  obtain ⟨lambda, htriple⟩ :=
    cubicTensor_zeroBinaryBlock_squareFactor_forces_tripleDet
      D hswap₁ hswap₂ hzero A B C hfactor
  have hA : A = lambda := by
    have h := (hfactor 1 0 0).symm.trans (htriple 1 0 0)
    simpa using h
  have hB : A + B = lambda := by
    have h := (hfactor 1 1 0).symm.trans (htriple 1 1 0)
    simpa using h
  have hC : A + C = lambda := by
    have h := (hfactor 1 0 1).symm.trans (htriple 1 0 1)
    simpa using h
  constructor
  · linear_combination hB - hA
  · linear_combination hC - hA

end
end HC4.Polynomial.RankThreeCubic
