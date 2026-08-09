import HC4.Newton.TerminalTwoZeroDoublingForm
import HC4.PlanarJC2Interface

/-!
# Two-zero terminal endpoint interface

After Phase 93.28's support calculation the remaining planar endpoint task
is no longer a general torus theorem.

The terminal fibre has two ambient coefficient polynomials

    A = pderiv 2 F,
    C = pderiv 3 F

which depend only on variables `0,1`, and

    F = X₂ A + X₃ C.

The next step is purely representational/algebraic:

1. descend `A,C` from the ambient four-variable ring to an actual
   `PlanarPolynomialMap K`;
2. prove that the constant four-dimensional Hessian determinant is the
   square of that planar Jacobian determinant;
3. invoke `PlanarJC2Injectivity`;
4. feed the resulting injectivity to `PlanarDoublingInjectivity`.

This file names that residual certificate so the later endpoint adapter has
a small explicit target.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

def HasAmbientPlanarDoublingData
    (F : MvPolynomial (Fin 4) K) : Prop :=
  HasStandardTwoZeroDoublingForm F ∧
  MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 2 F) = 0 ∧
  MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 2 F) = 0 ∧
  MvPolynomial.pderiv 2
      (MvPolynomial.pderiv 3 F) = 0 ∧
  MvPolynomial.pderiv 3
      (MvPolynomial.pderiv 3 F) = 0

theorem nonnegativeTerminalFace_two_standard_zeros_ambientPlanarData
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0) :
    HasAmbientPlanarDoublingData F := by
  refine ⟨
    nonnegativeTerminalFace_two_standard_zeros_hasDoublingForm
      hface hnonneg h0 h1,
    ?_⟩
  exact
    nonnegativeTerminalFace_two_standard_zeros_positiveHessian_zero
      hface hnonneg h0 h1

end

end HC4.Newton
