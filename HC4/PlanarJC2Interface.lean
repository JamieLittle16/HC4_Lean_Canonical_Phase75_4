import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Planar Jacobian-conjecture injectivity interface

The HC4 restart proof only needs injectivity of a planar Keller map at the
doubling endpoint.  This file gives that assumption an explicit Lean type
instead of leaving `JC2` as prose.

A planar polynomial map is represented by its two coordinate polynomials.
Its Jacobian determinant is written explicitly as the 2x2 cross
determinant of the partial derivatives.

`PlanarJC2Injectivity K` says that every planar polynomial map with nonzero
constant Jacobian determinant is injective on `K^2`.

This is the exact consequence of the usual planar Jacobian conjecture used
by the terminal Hessian-doubling argument.
-/

namespace HC4

noncomputable section

variable {K : Type*} [Field K]

abbrev Point2 (K : Type*) := Fin 2 -> K

abbrev PlanarPolynomialMap
    (K : Type*) [CommSemiring K] :=
  Fin 2 -> MvPolynomial (Fin 2) K

def planarPolynomialMapEval
    (G : PlanarPolynomialMap K)
    (u : Point2 K) :
    Point2 K :=
  fun i => MvPolynomial.eval u (G i)

def planarJacobianDetPolynomial
    (G : PlanarPolynomialMap K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.pderiv 0 (G 0) *
      MvPolynomial.pderiv 1 (G 1) -
    MvPolynomial.pderiv 1 (G 0) *
      MvPolynomial.pderiv 0 (G 1)

def HasNonzeroConstantPlanarJacobian
    (G : PlanarPolynomialMap K) : Prop :=
  ∃ c : K,
    c ≠ 0 ∧
    planarJacobianDetPolynomial G =
      MvPolynomial.C c

/-- The injectivity consequence of the planar Jacobian conjecture. -/
def PlanarJC2Injectivity (K : Type*) [Field K] : Prop :=
  ∀ G : PlanarPolynomialMap K,
    HasNonzeroConstantPlanarJacobian G ->
      Function.Injective
        (planarPolynomialMapEval G)

/-- Direct elimination rule for the JC2 injectivity interface. -/
theorem planar_injective_of_JC2
    (hJC2 : PlanarJC2Injectivity K)
    (G : PlanarPolynomialMap K)
    (hKeller :
      HasNonzeroConstantPlanarJacobian G) :
    Function.Injective
      (planarPolynomialMapEval G) :=
  hJC2 G hKeller

/-- Evaluating a constant-Jacobian certificate keeps the cross determinant
equal to the same nonzero scalar. -/
theorem planarJacobian_crossDet_eval_ne_zero
    (G : PlanarPolynomialMap K)
    (hKeller :
      HasNonzeroConstantPlanarJacobian G)
    (u : Point2 K) :
    MvPolynomial.eval u
      (planarJacobianDetPolynomial G) ≠ 0 := by
  rcases hKeller with ⟨c, hc, hdet⟩
  rw [hdet]
  simpa using hc

end

end HC4
