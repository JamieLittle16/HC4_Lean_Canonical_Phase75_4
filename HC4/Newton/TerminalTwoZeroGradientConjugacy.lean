import HC4.Newton.TerminalTwoZeroKellerReduction
import HC4.PlanarJacobianEvaluation
import HC4.PlanarDoublingInjectivity
import Mathlib.Tactic

/-!
# Gradient conjugacy for the two-zero terminal fibre

Let

    F = X₂ A(X₀,X₁) + X₃ C(X₀,X₁)

and let `A₂,C₂` be planar polynomials whose standard renames are `A,C`.

Split a point of `K^4` as

    u = (x₀,x₁),
    v = (x₂,x₃).

Then the terminal gradient is exactly

    (u,v) |-> ( v^T J_G(u), G(u) ),

where `G = (A₂,C₂)` and `J_G` is its evaluated planar Jacobian matrix.

This file proves that equality as an exact conjugacy under the standard
coordinate split.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Standard inclusion of the positive/fibre pair into `Fin 4`. -/
def standardPositivePairEmbedding : Fin 2 -> Fin 4
  | 0 => 2
  | 1 => 3

@[simp] theorem standardPositivePairEmbedding_zero :
    standardPositivePairEmbedding (0 : Fin 2) = (2 : Fin 4) := rfl

@[simp] theorem standardPositivePairEmbedding_one :
    standardPositivePairEmbedding (1 : Fin 2) = (3 : Fin 4) := rfl

/-- Base coordinates `(x₀,x₁)` of a four-dimensional point. -/
def standardBasePoint
    (p : Fin 4 -> K) :
    HC4.Point2 K :=
  fun i => p (standardZeroPairEmbedding i)

/-- Fibre coordinates `(x₂,x₃)` of a four-dimensional point. -/
def standardFibrePoint
    (p : Fin 4 -> K) :
    HC4.Point2 K :=
  fun i => p (standardPositivePairEmbedding i)

/-- Standard splitting `K^4 -> K^2 × K^2`. -/
def standardSplitPoint
    (p : Fin 4 -> K) :
    HC4.Point2 K × HC4.Point2 K :=
  (standardBasePoint p, standardFibrePoint p)

/-- Joining the standard split recovers the original four-dimensional
point. -/
theorem standardJoinPoint_split
    (p : Fin 4 -> K) :
    standardJoinPoint (standardSplitPoint p) = p := by
  funext i
  fin_cases i <;> rfl

/-- Splitting a joined planar base/fibre pair recovers that pair. -/
theorem standardSplitPoint_join
    (u v : HC4.Point2 K) :
    standardSplitPoint
        (standardJoinPoint (u, v)) =
      (u, v) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

/-- The standard split map is injective. -/
theorem standardSplitPoint_injective :
    Function.Injective
      (standardSplitPoint :
        (Fin 4 -> K) ->
          HC4.Point2 K × HC4.Point2 K) := by
  intro p q hpq
  rw [← standardJoinPoint_split p]
  rw [← standardJoinPoint_split q]
  exact congrArg standardJoinPoint hpq

/-- Renaming a planar polynomial and evaluating at an arbitrary four-point
is evaluation at the standard base pair. -/
theorem eval_rename_standardZeroPair_at
    (P : MvPolynomial (Fin 2) K)
    (p : Fin 4 -> K) :
    MvPolynomial.eval p
        (MvPolynomial.rename
          standardZeroPairEmbedding P) =
      MvPolynomial.eval
        (standardBasePoint p) P := by
  rw [MvPolynomial.eval_rename]
  rfl

/-- Evaluation of the renamed planar partial derivative agrees with the
corresponding ambient partial derivative of `A`. -/
theorem eval_pderiv_standardTwoZeroA_eq_planar
    {F : MvPolynomial (Fin 4) K}
    {A : MvPolynomial (Fin 2) K}
    (hA :
      MvPolynomial.rename
          standardZeroPairEmbedding A =
        standardTwoZeroA F)
    (p : Fin 4 -> K)
    (i : Fin 2) :
    MvPolynomial.eval p
        (MvPolynomial.pderiv
          (standardZeroPairEmbedding i)
          (standardTwoZeroA F)) =
      MvPolynomial.eval
        (standardBasePoint p)
        (MvPolynomial.pderiv i A) := by
  rw [← hA]
  rw [MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective i A]
  exact
    eval_rename_standardZeroPair_at
      (MvPolynomial.pderiv i A) p

/-- The analogous derivative evaluation identity for `C`. -/
theorem eval_pderiv_standardTwoZeroC_eq_planar
    {F : MvPolynomial (Fin 4) K}
    {C : MvPolynomial (Fin 2) K}
    (hC :
      MvPolynomial.rename
          standardZeroPairEmbedding C =
        standardTwoZeroC F)
    (p : Fin 4 -> K)
    (i : Fin 2) :
    MvPolynomial.eval p
        (MvPolynomial.pderiv
          (standardZeroPairEmbedding i)
          (standardTwoZeroC F)) =
      MvPolynomial.eval
        (standardBasePoint p)
        (MvPolynomial.pderiv i C) := by
  rw [← hC]
  rw [MvPolynomial.pderiv_rename
      standardZeroPairEmbedding.injective i C]
  exact
    eval_rename_standardZeroPair_at
      (MvPolynomial.pderiv i C) p

/-- The positive half of the four-dimensional gradient is exactly the
planar base map `(A,C)`. -/
theorem standardTwoZero_gradient_positive_eq_planar
    {F : MvPolynomial (Fin 4) K}
    {A C : MvPolynomial (Fin 2) K}
    (hA :
      MvPolynomial.rename
          standardZeroPairEmbedding A =
        standardTwoZeroA F)
    (hC :
      MvPolynomial.rename
          standardZeroPairEmbedding C =
        standardTwoZeroC F)
    (p : Fin 4 -> K) :
    standardFibrePoint
        (mvGradientMap F p) =
      HC4.planarPolynomialMapEval
        (standardPlanarPairMap A C)
        (standardBasePoint p) := by
  funext i
  fin_cases i
  · change
      MvPolynomial.eval p
          (MvPolynomial.pderiv 2 F) =
        MvPolynomial.eval
          (standardBasePoint p) A
    rw [standardTwoZero_pderiv_two_eq_A]
    rw [← hA]
    exact eval_rename_standardZeroPair_at A p
  · change
      MvPolynomial.eval p
          (MvPolynomial.pderiv 3 F) =
        MvPolynomial.eval
          (standardBasePoint p) C
    rw [standardTwoZero_pderiv_three_eq_C]
    rw [← hC]
    exact eval_rename_standardZeroPair_at C p

/-- The zero-weight half of the gradient is the row-vector action of the
evaluated planar Jacobian on the fibre coordinates. -/
theorem standardTwoZero_gradient_zero_eq_vecMul
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {A C : MvPolynomial (Fin 2) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hA :
      MvPolynomial.rename
          standardZeroPairEmbedding A =
        standardTwoZeroA F)
    (hC :
      MvPolynomial.rename
          standardZeroPairEmbedding C =
        standardTwoZeroC F)
    (p : Fin 4 -> K) :
    standardBasePoint
        (mvGradientMap F p) =
      Matrix.vecMul
        (standardFibrePoint p)
        (HC4.planarJacobianMatrixAt
          (standardPlanarPairMap A C)
          (standardBasePoint p)) := by
  funext i
  fin_cases i
  · change
      MvPolynomial.eval p
          (MvPolynomial.pderiv 0 F) =
        Matrix.vecMul
          (standardFibrePoint p)
          (HC4.planarJacobianMatrixAt
            (standardPlanarPairMap A C)
            (standardBasePoint p))
          0
    rw [standardTwoZero_pderiv_zero_formula hd hhom]
    simp only [map_add, map_mul,
      MvPolynomial.eval_X]
    have hA0 :
        MvPolynomial.eval p
            (MvPolynomial.pderiv 0
              (standardTwoZeroA F)) =
          MvPolynomial.eval
            (standardBasePoint p)
            (MvPolynomial.pderiv 0 A) := by
      simpa using
        (eval_pderiv_standardTwoZeroA_eq_planar
          hA p (0 : Fin 2))
    have hC0 :
        MvPolynomial.eval p
            (MvPolynomial.pderiv 0
              (standardTwoZeroC F)) =
          MvPolynomial.eval
            (standardBasePoint p)
            (MvPolynomial.pderiv 0 C) := by
      simpa using
        (eval_pderiv_standardTwoZeroC_eq_planar
          hC p (0 : Fin 2))
    rw [hA0, hC0]
    simp [Matrix.vecMul, dotProduct,
      HC4.planarJacobianMatrixAt,
      standardFibrePoint,
      standardPlanarPairMap]
  · change
      MvPolynomial.eval p
          (MvPolynomial.pderiv 1 F) =
        Matrix.vecMul
          (standardFibrePoint p)
          (HC4.planarJacobianMatrixAt
            (standardPlanarPairMap A C)
            (standardBasePoint p))
          1
    rw [standardTwoZero_pderiv_one_formula hd hhom]
    simp only [map_add, map_mul,
      MvPolynomial.eval_X]
    have hA1 :
        MvPolynomial.eval p
            (MvPolynomial.pderiv 1
              (standardTwoZeroA F)) =
          MvPolynomial.eval
            (standardBasePoint p)
            (MvPolynomial.pderiv 1 A) := by
      simpa using
        (eval_pderiv_standardTwoZeroA_eq_planar
          hA p (1 : Fin 2))
    have hC1 :
        MvPolynomial.eval p
            (MvPolynomial.pderiv 1
              (standardTwoZeroC F)) =
          MvPolynomial.eval
            (standardBasePoint p)
            (MvPolynomial.pderiv 1 C) := by
      simpa using
        (eval_pderiv_standardTwoZeroC_eq_planar
          hC p (1 : Fin 2))
    rw [hA1, hC1]
    simp [Matrix.vecMul, dotProduct,
      HC4.planarJacobianMatrixAt,
      standardFibrePoint,
      standardPlanarPairMap]

/-- Exact conjugacy between the actual terminal gradient and the abstract
doubling map under the standard coordinate split. -/
theorem standardTwoZero_gradient_conjugacy
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {A C : MvPolynomial (Fin 2) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hA :
      MvPolynomial.rename
          standardZeroPairEmbedding A =
        standardTwoZeroA F)
    (hC :
      MvPolynomial.rename
          standardZeroPairEmbedding C =
        standardTwoZeroC F)
    (p : Fin 4 -> K) :
    standardSplitPoint
        (mvGradientMap F p) =
      HC4.doublingGradientMap
        (HC4.planarPolynomialMapEval
          (standardPlanarPairMap A C))
        (HC4.planarJacobianMatrixAt
          (standardPlanarPairMap A C))
        (fun _ _ => (0 : K))
        (standardSplitPoint p) := by
  apply Prod.ext
  · simpa [standardSplitPoint,
      HC4.doublingGradientMap] using
      (standardTwoZero_gradient_zero_eq_vecMul
        hd hhom hA hC p)
  · simpa [standardSplitPoint,
      HC4.doublingGradientMap] using
      (standardTwoZero_gradient_positive_eq_planar
        hA hC p)

end

end HC4.Newton
