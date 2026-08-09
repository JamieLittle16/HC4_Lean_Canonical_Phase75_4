import HC4.Newton.TerminalScalarGradient
import HC4.Newton.TerminalCenteredWeights

/-!
# Terminal direct-rank-jump reduction

This module combines the green terminal conformal-face dichotomy with the
new scalar-gradient and centred-weight lemmas.

For a nontrivial weighted terminal fibre with nondegenerate actual Hessian:

* either the gradient is injective immediately (the scalar branch);
* or the terminal face is genuinely non-scalar and carries a distinct
  nonzero opposite pair of centred weights.

If the terminal fibre also contains a distinct exact gradient collision,
the injective branch is impossible.  Therefore every surviving terminal
direct-rank-jump obstruction is forced into the explicit non-scalar
opposite-pair configuration.

This is an honest reduction, not the final non-scalar endpoint theorem.
It closes the scalar direct-jump branch completely and sharply isolates the
remaining terminal classification problem.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The exact residual structure of a non-scalar terminal direct jump in
four coordinates. -/
def HasResidualNonScalarTerminalJump
    (lambda : Fin 4 -> ℤ)
    (d : ℤ)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  HasNonScalarTerminalConformalFace
      (0 : Fin 4) 1 2 3 lambda d F ∧
    ∃ r c : Fin 4,
      centeredTerminalWeight lambda d r ≠ 0 ∧
      centeredTerminalWeight lambda d c =
        - centeredTerminalWeight lambda d r ∧
      r ≠ c

/-- Every non-scalar terminal conformal face supplies the residual
opposite-pair certificate. -/
theorem nonScalarTerminalFace_hasResidualJump
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F) :
    HasResidualNonScalarTerminalJump
      lambda d F := by
  refine ⟨hface, ?_⟩
  exact
    nonScalarTerminalConformalFace_exists_nonzero_opposite_pair
      hface

/-- **Terminal direct-jump reduction.**
Before using an exact collision, the terminal conformal face is either
already injective or belongs to the explicit residual non-scalar branch. -/
theorem terminalDirectRankJump_injective_or_residual
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hnontrivial :
      IsNontrivialIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F) :
    Function.Injective (mvGradientMap F) ∨
      HasResidualNonScalarTerminalJump
        lambda d F := by
  rcases
      terminalConformalFace_dichotomy
        (0 : Fin 4) 1 2 3
        hnontrivial hhom hdet with
    hscalar | hnonscalar
  · left
    exact
      pureQuadratic_actualHessian_gradient_injective
        hscalar.2 hdet
  · right
    exact
      nonScalarTerminalFace_hasResidualJump
        hnonscalar

/-- A distinct exact terminal collision eliminates the scalar/injective
branch.  Hence every surviving direct-rank-jump obstruction is genuinely
non-scalar and has a nonzero opposite centred-weight pair. -/
theorem terminalDirectRankJump_collision_forces_residual
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
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
    HasResidualNonScalarTerminalJump
      lambda d F := by
  rcases
      terminalDirectRankJump_injective_or_residual
        hnontrivial hhom hdet with
    hinj | hresidual
  · exact False.elim
      (exactGradientCollision_impossible_of_injective
        F p q hpq hinj hcoll)
  · exact hresidual

/-- Expanded form of the residual terminal obstruction, convenient for the
next endpoint classification module. -/
theorem terminalDirectRankJump_collision_forces_opposite_pair
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
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
    IsNonScalarIntegralWeight lambda ∧
      ∃ r c : Fin 4,
        centeredTerminalWeight lambda d r ≠ 0 ∧
        centeredTerminalWeight lambda d c =
          - centeredTerminalWeight lambda d r ∧
        r ≠ c := by
  have hresidual :=
    terminalDirectRankJump_collision_forces_residual
      hnontrivial hhom hdet
      p q hpq hcoll
  exact
    ⟨hresidual.1.2.1, hresidual.2⟩

end

end HC4.Newton
