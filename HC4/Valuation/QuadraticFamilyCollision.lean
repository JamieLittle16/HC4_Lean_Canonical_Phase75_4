import HC4.Valuation.KernelInflationHessianDefect
import HC4.Valuation.PolynomialFamilyCollisionSpecialFiber
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Quadratic polynomial families cannot carry an exact collision

Let the coefficient ring be an integral domain.  A source-homogeneous
quadratic multivariate polynomial has a linear gradient.  Its constant source
Hessian matrix therefore represents the gradient map exactly.  If that matrix
has nonzero determinant, the domain-level matrix kernel theorem forces equal
gradients to have equal source points.

For the HC4 parameter family the coefficient ring is `Polynomial K` and the
exact Hessian defect is `X^Delta`, which is nonzero.  Hence a degree-two
canonical family cannot carry the two distinct moving sections retained by the
restart frontier.
-/

namespace HC4.Valuation

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Source Hessian of a quadratic family, with the source variables evaluated
at the origin but the coefficient ring left untouched. -/
noncomputable def quadraticFamilyHessianMatrix
    (P : MvPolynomial (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j =>
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i P))

/-- A homogeneous degree-zero multivariate polynomial over a commutative ring
is its constant coefficient. -/
theorem homogeneous_zero_eq_C_constantCoeff_domain
    {P : MvPolynomial (Fin 4) R}
    (hzero : P.IsHomogeneous 0) :
    P = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · subst d
    have hconst :
        MvPolynomial.constantCoeff P = MvPolynomial.coeff 0 P := by
      exact
        congrArg
          (fun f : MvPolynomial (Fin 4) R → R => f P)
          MvPolynomial.constantCoeff_eq
    simp [hconst]
  · have hdeg : Finsupp.degree d ≠ 0 := by
      intro hdegree
      exact hd ((Finsupp.degree_eq_zero_iff d).mp hdegree)
    have hcoeff : MvPolynomial.coeff d P = 0 :=
      hzero.coeff_eq_zero hdeg
    simp [hcoeff, hd, Ne.symm hd]

/-- Every second derivative of a homogeneous quadratic family is constant in
the source variables. -/
theorem homogeneous_two_secondDerivative_eq_C_familyHessian
    {P : MvPolynomial (Fin 4) R}
    (hhom : P.IsHomogeneous 2)
    (i j : Fin 4) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i P) =
      MvPolynomial.C (quadraticFamilyHessianMatrix P i j) := by
  have hfirst : (MvPolynomial.pderiv i P).IsHomogeneous 1 := by
    simpa using hhom.pderiv
  have hsecond :
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)).IsHomogeneous 0 := by
    simpa using hfirst.pderiv
  calc
    MvPolynomial.pderiv j (MvPolynomial.pderiv i P) =
        MvPolynomial.C
          (MvPolynomial.constantCoeff
            (MvPolynomial.pderiv j (MvPolynomial.pderiv i P))) :=
      homogeneous_zero_eq_C_constantCoeff_domain hsecond
    _ = MvPolynomial.C (quadraticFamilyHessianMatrix P i j) := by
      rfl

/-- Euler's identity writes the gradient of a quadratic family as Hessian
matrix multiplication over the coefficient domain. -/
theorem homogeneous_two_gradient_eq_mulVec_domain
    {P : MvPolynomial (Fin 4) R}
    (hhom : P.IsHomogeneous 2)
    (p : Fin 4 → R) :
    (fun i => MvPolynomial.eval p (MvPolynomial.pderiv i P)) =
      Matrix.mulVec (quadraticFamilyHessianMatrix P) p := by
  funext i
  have hfirst : (MvPolynomial.pderiv i P).IsHomogeneous 1 := by
    simpa using hhom.pderiv
  have heuler :
      (∑ j : Fin 4,
        MvPolynomial.X j *
          MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) =
        MvPolynomial.pderiv i P := by
    simpa using hfirst.sum_X_mul_pderiv
  calc
    MvPolynomial.eval p (MvPolynomial.pderiv i P) =
        MvPolynomial.eval p
          (∑ j : Fin 4,
            MvPolynomial.X j *
              MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) := by
      exact congrArg (MvPolynomial.eval p) heuler.symm
    _ = ∑ j : Fin 4, (quadraticFamilyHessianMatrix P i j) * p j := by
      rw [map_sum
        (MvPolynomial.eval p)
        (fun j : Fin 4 =>
          MvPolynomial.X j *
            MvPolynomial.pderiv j (MvPolynomial.pderiv i P))
        Finset.univ]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul]
      rw [homogeneous_two_secondDerivative_eq_C_familyHessian hhom i j]
      simp [mul_comm]
    _ = Matrix.mulVec (quadraticFamilyHessianMatrix P) p i := by
      simp [Matrix.mulVec, dotProduct]

/-- The determinant of the constant source Hessian is the source-constant
coefficient of the polynomial Hessian determinant. -/
theorem quadraticFamilyHessianMatrix_det
    (P : MvPolynomial (Fin 4) R) :
    (quadraticFamilyHessianMatrix P).det =
      MvPolynomial.constantCoeff (HC4.Polynomial.hessianDeterminant P) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [RingHom.map_det]
  rfl

/-- Over an integral domain, nonzero Hessian determinant makes the quadratic
gradient injective. -/
theorem homogeneous_two_exactGradientCollision_eq_domain
    {P : MvPolynomial (Fin 4) R}
    (hhom : P.IsHomogeneous 2)
    (a b : Fin 4 → R)
    (hcoll :
      ∀ i : Fin 4,
        MvPolynomial.eval a (MvPolynomial.pderiv i P) =
          MvPolynomial.eval b (MvPolynomial.pderiv i P))
    (hdet : (quadraticFamilyHessianMatrix P).det ≠ 0) :
    a = b := by
  have hgrad :
      Matrix.mulVec (quadraticFamilyHessianMatrix P) a =
        Matrix.mulVec (quadraticFamilyHessianMatrix P) b := by
    rw [← homogeneous_two_gradient_eq_mulVec_domain hhom a]
    rw [← homogeneous_two_gradient_eq_mulVec_domain hhom b]
    funext i
    exact hcoll i
  by_contra hab
  let v : Fin 4 → R := fun i => a i - b i
  have hvne : v ≠ 0 := by
    intro hv
    apply hab
    funext i
    have hi := congrFun hv i
    dsimp [v] at hi
    exact sub_eq_zero.mp hi
  have hvzero :
      Matrix.mulVec (quadraticFamilyHessianMatrix P) v = 0 := by
    funext i
    calc
      Matrix.mulVec (quadraticFamilyHessianMatrix P) v i =
          Matrix.mulVec (quadraticFamilyHessianMatrix P) a i -
            Matrix.mulVec (quadraticFamilyHessianMatrix P) b i := by
        simp [v, Matrix.mulVec, dotProduct,
          Finset.sum_sub_distrib, mul_sub]
      _ = 0 := sub_eq_zero.mpr (congrFun hgrad i)
  have hdet0 : (quadraticFamilyHessianMatrix P).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := quadraticFamilyHessianMatrix P)).mp
      ⟨v, hvne, hvzero⟩
  exact hdet hdet0

section PolynomialParameter

variable {K : Type*} [Field K]

/-- A homogeneous quadratic polynomial-parameter family with pure Hessian
clock `X^Delta` cannot carry two distinct exact-collision sections. -/
theorem quadraticPolynomialFamily_exactCollision_sections_eq
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hhom : P.IsHomogeneous 2)
    (a b : Fin 4 → Polynomial K)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hcoll : HasPolynomialFamilyExactGradientCollision P a b) :
    a = b := by
  have hdetEq :
      (quadraticFamilyHessianMatrix P).det = Polynomial.X ^ Delta := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [hdef]
    simp
  have hdet : (quadraticFamilyHessianMatrix P).det ≠ 0 := by
    rw [hdetEq]
    exact pow_ne_zero _ Polynomial.X_ne_zero
  exact
    homogeneous_two_exactGradientCollision_eq_domain
      hhom a b hcoll hdet

end PolynomialParameter

end

end HC4.Valuation
