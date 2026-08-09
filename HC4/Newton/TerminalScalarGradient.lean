import HC4.Newton.TerminalConformalFace
import HC4.Newton.TerminalCollision
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Scalar terminal gradient

Phase 93.25 proves that the scalar terminal-weight branch has pure ordinary
quadratic support.  This module closes that branch completely.

For a four-variable polynomial with pure quadratic support:

1. it is homogeneous of ordinary degree two;
2. each second derivative is homogeneous of degree zero, hence constant;
3. Euler's identity applied to each first derivative gives

       grad F(p) = p^T Hess F(0);

4. nonzero determinant of the actual Hessian makes this vector-matrix map
   injective.

Thus a scalar terminal fibre with nondegenerate actual Hessian has an
injective gradient, and therefore cannot carry a distinct exact collision.

This uses the actual Hessian already constructed in Phase 93.24 and does
not invoke any torus classification.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Pure quadratic support implies ordinary homogeneity of degree two. -/
theorem hasPureQuadraticSupport_isHomogeneous_two
    {F : MvPolynomial (Fin 4) K}
    (hquad : HasPureQuadraticSupport F) :
    F.IsHomogeneous 2 := by
  unfold MvPolynomial.IsHomogeneous
  unfold MvPolynomial.IsWeightedHomogeneous
  intro m hm
  have hz :
      integralOrdinaryDegree m = 2 :=
    hquad m hm
  unfold integralOrdinaryDegree at hz
  rw [Finsupp.weight_apply]
  simp only [Pi.one_apply, nsmul_eq_mul, mul_one]
  exact_mod_cast hz

/-- A homogeneous polynomial of degree zero is its constant coefficient. -/
theorem homogeneous_zero_eq_C_constantCoeff
    {P : MvPolynomial (Fin 4) K}
    (hzero : P.IsHomogeneous 0) :
    P = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · subst d
    have hconst :
        MvPolynomial.constantCoeff P =
          MvPolynomial.coeff 0 P := by
      exact
        congrArg
          (fun f : MvPolynomial (Fin 4) K -> K => f P)
          MvPolynomial.constantCoeff_eq
    simp [hconst]
  · have hdeg :
        Finsupp.degree d ≠ 0 := by
      intro hdegree
      exact hd
        ((Finsupp.degree_eq_zero_iff d).mp hdegree)
    have hcoeff :
        MvPolynomial.coeff d P = 0 :=
      hzero.coeff_eq_zero hdeg
    simp [hcoeff, hd, Ne.symm hd]

/-- For an ordinary quadratic polynomial, every second derivative is the
constant equal to its value at the origin. -/
theorem homogeneous_two_secondDerivative_eq_C_hessianOrigin
    {F : MvPolynomial (Fin 4) K}
    (hhom : F.IsHomogeneous 2)
    (i j : Fin 4) :
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i F) =
      MvPolynomial.C
        (mvHessianComponentAt
          (fun _ => (0 : K)) F j i) := by
  have hfirst :
      (MvPolynomial.pderiv i F).IsHomogeneous 1 := by
    simpa using hhom.pderiv
  have hsecond :
      (MvPolynomial.pderiv j
        (MvPolynomial.pderiv i F)).IsHomogeneous 0 := by
    simpa using hfirst.pderiv
  calc
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i F) =
      MvPolynomial.C
        (MvPolynomial.constantCoeff
          (MvPolynomial.pderiv j
            (MvPolynomial.pderiv i F))) :=
      homogeneous_zero_eq_C_constantCoeff hsecond
    _ =
      MvPolynomial.C
        (mvHessianComponentAt
          (fun _ => (0 : K)) F j i) := by
      congr 1
      unfold mvHessianComponentAt
      rw [MvPolynomial.eval_zero']

/-- The actual Hessian at the origin, indexed directly by `Fin 4`. -/
def standardActualHessianMatrix
    (F : MvPolynomial (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j =>
    mvHessianComponentAt
      (fun _ => (0 : K)) F i j

/-- The four-coordinate terminal Hessian with coordinates `0,1,2,3` is the
standard actual Hessian matrix. -/
theorem terminalActualHessianMatrix_standard_eq
    (F : MvPolynomial (Fin 4) K) :
    terminalActualHessianMatrix
        (0 : Fin 4) 1 2 3 F =
      standardActualHessianMatrix F := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Euler identity for a quadratic potential, written as an exact
vector-matrix formula for its gradient. -/
theorem homogeneous_two_gradient_eq_vecMul
    {F : MvPolynomial (Fin 4) K}
    (hhom : F.IsHomogeneous 2)
    (p : Fin 4 -> K) :
    mvGradientAt p F =
      Matrix.vecMul p
        (standardActualHessianMatrix F) := by
  funext i
  unfold mvGradientAt
  unfold mvGradientComponentAt
  have hfirst :
      (MvPolynomial.pderiv i F).IsHomogeneous 1 := by
    simpa using hhom.pderiv
  have heuler :
      (∑ j : Fin 4,
        MvPolynomial.X j *
          MvPolynomial.pderiv j
            (MvPolynomial.pderiv i F)) =
        MvPolynomial.pderiv i F := by
    simpa using hfirst.sum_X_mul_pderiv
  calc
    MvPolynomial.eval p
        (MvPolynomial.pderiv i F) =
      MvPolynomial.eval p
        (∑ j : Fin 4,
          MvPolynomial.X j *
            MvPolynomial.pderiv j
              (MvPolynomial.pderiv i F)) := by
        exact congrArg (MvPolynomial.eval p) heuler.symm
    _ =
      ∑ j : Fin 4,
        p j *
          mvHessianComponentAt
            (fun _ => (0 : K)) F j i := by
        rw [map_sum
          (MvPolynomial.eval p)
          (fun j : Fin 4 =>
            MvPolynomial.X j *
              MvPolynomial.pderiv j
                (MvPolynomial.pderiv i F))
          Finset.univ]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_mul]
        rw [homogeneous_two_secondDerivative_eq_C_hessianOrigin
          hhom i j]
        simp
    _ =
      Matrix.vecMul p
        (standardActualHessianMatrix F) i := by
        simp [Matrix.vecMul, standardActualHessianMatrix,
          dotProduct]

/-- Nonzero determinant of the standard actual Hessian makes the associated
row-vector multiplication injective. -/
theorem standardActualHessian_vecMul_injective
    (F : MvPolynomial (Fin 4) K)
    (hdet :
      Matrix.det
        (standardActualHessianMatrix F) ≠ 0) :
    Function.Injective
      (fun p : Fin 4 -> K =>
        Matrix.vecMul p
          (standardActualHessianMatrix F)) := by
  have hunitDet :
      IsUnit
        (Matrix.det
          (standardActualHessianMatrix F)) := by
    exact isUnit_iff_ne_zero.mpr hdet
  have hunitMatrix :
      IsUnit (standardActualHessianMatrix F) :=
    (Matrix.isUnit_iff_isUnit_det
      (standardActualHessianMatrix F)).2 hunitDet
  exact
    Matrix.vecMul_injective_iff_isUnit.mpr
      hunitMatrix

/-- A pure quadratic four-variable potential with nondegenerate actual
Hessian has injective gradient. -/
theorem pureQuadratic_actualHessian_gradient_injective
    {F : MvPolynomial (Fin 4) K}
    (hquad : HasPureQuadraticSupport F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F) :
    Function.Injective (mvGradientMap F) := by
  have hhom :
      F.IsHomogeneous 2 :=
    hasPureQuadraticSupport_isHomogeneous_two hquad
  have hdetStd :
      Matrix.det
        (standardActualHessianMatrix F) ≠ 0 := by
    unfold HasNondegenerateTerminalActualHessian at hdet
    rw [terminalActualHessianMatrix_standard_eq] at hdet
    exact hdet
  have hlinj :=
    standardActualHessian_vecMul_injective
      F hdetStd
  intro p q hpq
  have hpq' :
      mvGradientAt p F = mvGradientAt q F := by
    simpa [mvGradientMap] using hpq
  apply hlinj
  change
    Matrix.vecMul p (standardActualHessianMatrix F) =
      Matrix.vecMul q (standardActualHessianMatrix F)
  rw [← homogeneous_two_gradient_eq_vecMul hhom p]
  rw [← homogeneous_two_gradient_eq_vecMul hhom q]
  exact hpq'

/-- The scalar terminal branch from Phase 93.25 has injective gradient. -/
theorem scalarTerminal_actualHessian_gradient_injective
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hscalar :
      IsScalarIntegralWeight lambda)
    (hnontrivial :
      IsNontrivialIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F) :
    Function.Injective (mvGradientMap F) := by
  have hendpoint :=
    scalarTerminal_actualHessian_endpoint_of_scalarWeight
      (0 : Fin 4) 1 2 3
      hscalar hnontrivial hhom hdet
  exact
    pureQuadratic_actualHessian_gradient_injective
      hendpoint.2 hdet

/-- A distinct exact collision rules out the scalar terminal direct-jump
branch completely. -/
theorem scalarTerminal_exactCollision_impossible
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hscalar :
      IsScalarIntegralWeight lambda)
    (hnontrivial :
      IsNontrivialIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F)
    (p q : Fin 4 -> K)
    (hpq : p ≠ q)
    (hcoll :
      HasExactGradientCollision F p q) :
    False := by
  exact
    exactGradientCollision_impossible_of_injective
      F p q hpq
      (scalarTerminal_actualHessian_gradient_injective
        hscalar hnontrivial hhom hdet)
      hcoll

end

end HC4.Newton
