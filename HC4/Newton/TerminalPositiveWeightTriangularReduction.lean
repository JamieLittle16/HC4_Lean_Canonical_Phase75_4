import HC4.Newton.PositiveWeightTriangularSupport

/-!
# Positive terminal triangular reduction

This module applies the positive-weight support theorem to the actual
non-scalar terminal face.

Given a complement-weight permutation

    lambda (π i) + lambda i = d,

the permuted gradient

    G_i = pderiv (π i) F

is weight-preserving.

If all terminal weights are strictly positive, every component of `G`
therefore has exact triangular support:

* its linear terms involve only variables of the same weight;
* every nonlinear monomial uses only variables of strictly smaller weight.

This is the precise finite recursion invariant used in the manuscript's
`k = 0` endpoint.  The next module only has to combine it with
nonsingularity of the linear part and induct over the finitely many weights.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Componentwise triangular support certificate for the determinant-matched
permuted terminal gradient. -/
def HasPositiveTerminalTriangularGradient
    (lambda : Fin 4 -> ℤ)
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ i : Fin 4,
    HasPositiveWeightTriangularSupport
      lambda (lambda i)
      (terminalPermutedGradient π F i)

/-- The strictly-positive non-scalar terminal face has a triangular
weight-preserving permuted gradient. -/
theorem positiveTerminalFace_hasTriangularPermutedGradient
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {π : Equiv.Perm (Fin 4)}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda) :
    HasPositiveTerminalTriangularGradient
      lambda π F := by
  intro i
  apply
    positiveWeightedHomogeneous_hasTriangularSupport
      hpos
  exact
    terminalPermutedGradient_component_weight
      hface.2.2.2.1 hπ i

/-- A determinant matching from Phase 93.27 therefore supplies some
positive triangular output permutation whenever all terminal weights are
strictly positive. -/
theorem positiveTerminalFace_existsTriangularPermutedGradient
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda) :
    ∃ π : Equiv.Perm (Fin 4),
      (∀ i : Fin 4,
        lambda (π i) + lambda i = d) ∧
      HasPositiveTerminalTriangularGradient
        lambda π F := by
  rcases
      nonScalarTerminalConformalFace_has_complementWeightPermutation
        hface with
    ⟨π, hπ⟩
  refine ⟨π, hπ, ?_⟩
  exact
    positiveTerminalFace_hasTriangularPermutedGradient
      hface hπ hpos

/-- Minimum-weight components of the matched terminal gradient are purely
linear in the minimum-weight variables. -/
theorem positiveTerminalFace_minimumWeight_component_linear
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    {π : Equiv.Perm (Fin 4)}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda)
    {i : Fin 4}
    (hmin :
      ∀ j : Fin 4,
        lambda i ≤ lambda j) :
    ∀ m : Fin 4 →₀ ℕ,
      MvPolynomial.coeff m
          (terminalPermutedGradient π F i) ≠ 0 ->
        ∃ j : Fin 4,
          m = Finsupp.single j 1 ∧
          lambda j = lambda i := by
  apply
    minimumPositiveWeight_support_is_linear
      hpos (hpos i) hmin
  exact
    terminalPermutedGradient_component_weight
      hface.2.2.2.1 hπ i

end

end HC4.Newton
