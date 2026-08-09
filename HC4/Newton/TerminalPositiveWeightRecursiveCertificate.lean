import HC4.Newton.TerminalPositiveWeightLinearBlocks

/-!
# Positive terminal linear-block package

The strictly-positive terminal branch now has both halves of the finite
recursive inversion mechanism:

* Phase 93.31:
  each determinant-matched gradient component is a same-weight linear part
  plus monomials in strictly lower weights;

* Phase 93.32:
  the global linear matrix is block diagonal by terminal weight and every
  equal-weight block has trivial kernel.

This module packages the two statements against the same matching
permutation.  The remaining endpoint theorem is purely the finite
minimal-weight argument on two points.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Full positive terminal recursion certificate for one determinant
matching. -/
def HasPositiveTerminalRecursiveCertificate
    (lambda : Fin 4 -> ℤ)
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) : Prop :=
  HasPositiveTerminalTriangularGradient lambda π F ∧
  Function.Injective
    (fun v : Fin 4 -> K =>
      Matrix.vecMul v
        (terminalPermutedHessianMatrix π F)) ∧
  (∀ j i : Fin 4,
    lambda j ≠ lambda i ->
      terminalPermutedHessianMatrix π F j i = 0)

/-- Every strictly-positive non-scalar terminal face supplies a complete
recursive certificate for some determinant-matching output permutation. -/
theorem positiveTerminalFace_existsRecursiveCertificate
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
      HasPositiveTerminalRecursiveCertificate
        lambda π F := by
  rcases
      positiveTerminalFace_existsTriangularPermutedGradient
        hface hpos with
    ⟨π, hπ, htri⟩
  refine ⟨π, hπ, htri, ?_, ?_⟩
  · exact
      terminalPermutedHessian_vecMul_injective
        π hface.2.2.1
  · intro j i hne
    exact
      terminalPermutedHessian_entry_eq_zero_of_weight_ne
        hface hπ hne

end

end HC4.Newton
