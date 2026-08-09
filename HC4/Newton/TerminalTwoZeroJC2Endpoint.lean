import HC4.Newton.TerminalTwoZeroGradientConjugacy
import HC4.Newton.TerminalCollision

/-!
# JC2 closes the standard two-zero terminal branch

This module completes the standard `k = 2` terminal endpoint.

The global Monge--Ampère identity produces an honest planar Keller map.
`PlanarJC2Injectivity` makes its base map injective.  The evaluated planar
Jacobian is nonsingular everywhere, so the abstract doubling map is
injective.  The exact gradient conjugacy then makes the original
four-dimensional terminal gradient injective.

A distinct exact terminal collision is therefore impossible.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The standard two-zero terminal gradient is injective under JC2. -/
theorem standardTwoZero_terminal_gradient_injective_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    Function.Injective (mvGradientMap F) := by
  rcases
      standardTwoZero_mongeAmpere_hasPlanarKellerModel
        hd hhom hMA with
    ⟨A, C, hA, hC, hKeller⟩
  let G : HC4.PlanarPolynomialMap K :=
    standardPlanarPairMap A C
  have hG :
      Function.Injective
        (HC4.planarPolynomialMapEval G) :=
    HC4.planar_injective_of_JC2
      hJC2 G hKeller
  have hJ :
      ∀ u : HC4.Point2 K,
        Matrix.det
          (HC4.planarJacobianMatrixAt G u) ≠ 0 := by
    intro u
    exact
      HC4.planarJacobianMatrixAt_det_ne_zero
        G hKeller u
  have hdoubling :
      Function.Injective
        (HC4.doublingGradientMap
          (HC4.planarPolynomialMapEval G)
          (HC4.planarJacobianMatrixAt G)
          (fun _ _ => (0 : K))) :=
    HC4.doublingGradientMap_injective_of_det_ne_zero
      (HC4.planarPolynomialMapEval G)
      (HC4.planarJacobianMatrixAt G)
      (fun _ _ => (0 : K))
      hG hJ
  intro p q hpq
  apply standardSplitPoint_injective
  apply hdoubling
  change
    HC4.doublingGradientMap
        (HC4.planarPolynomialMapEval G)
        (HC4.planarJacobianMatrixAt G)
        (fun _ _ => (0 : K))
        (standardSplitPoint p) =
      HC4.doublingGradientMap
        (HC4.planarPolynomialMapEval G)
        (HC4.planarJacobianMatrixAt G)
        (fun _ _ => (0 : K))
        (standardSplitPoint q)
  rw [← standardTwoZero_gradient_conjugacy
      hd hhom hA hC p]
  rw [← standardTwoZero_gradient_conjugacy
      hd hhom hA hC q]
  exact congrArg standardSplitPoint hpq

/-- Direct conformal-terminal form: two standard zero weights plus
nonnegativity and the global Monge--Ampère equation imply terminal-gradient
injectivity under JC2. -/
theorem nonnegativeTerminalFace_two_standard_zeros_gradient_injective_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F) :
    Function.Injective (mvGradientMap F) := by
  have hd :
      0 < d :=
    nonnegativeTerminalFace_two_standard_zeros_degree_pos
      hface hnonneg h0 h1
  have hlambda :
      lambda =
        standardTwoZeroTerminalWeight d :=
    nonnegativeTerminalFace_two_standard_zeros_weight_eq
      hface hnonneg h0 h1
  have hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F := by
    rw [← hlambda]
    exact hface.2.2.2.1
  exact
    standardTwoZero_terminal_gradient_injective_of_JC2
      hJC2 hd hhom hMA

/-- **Closed standard two-zero endpoint.**
A distinct exact collision cannot survive the standard two-zero terminal
branch under JC2. -/
theorem nonnegativeTerminalFace_two_standard_zeros_collision_impossible_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0)
    (hMA :
      HC4.MongeAmpere.IsPolynomialMongeAmpere F)
    (p q : Fin 4 -> K)
    (hpq : p ≠ q)
    (hcoll :
      HasExactGradientCollision F p q) :
    False := by
  exact
    exactGradientCollision_impossible_of_injective
      F p q hpq
      (nonnegativeTerminalFace_two_standard_zeros_gradient_injective_of_JC2
        hJC2 hface hnonneg h0 h1 hMA)
      hcoll

end

end HC4.Newton
