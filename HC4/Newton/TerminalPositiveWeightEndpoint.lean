import HC4.Newton.PositiveWeightTriangularEvaluation
import HC4.Newton.TerminalCollision
import Mathlib.Tactic

/-!
# Closure of the strictly-positive terminal branch

This is the finite recursive inverse promised by the positive-weight
terminal argument.

Suppose all terminal weights are strictly positive.  For a
determinant-matching permutation `π`, the permuted gradient is
weight-preserving and triangular.

Given two points with the same permuted-gradient value, prove coordinate
equality by strong induction on the positive integer terminal weight.

At weight `t`:

1. the induction hypothesis gives equality in every lower-weight
   coordinate;
2. Phase 93.33's evaluation theorem cancels every nonlinear term in all
   weight-`t` output components;
3. only the weight-`t` linear Hessian block remains;
4. Phase 93.32 proves that block has trivial kernel;
5. therefore the two points agree on the entire weight-`t` coordinate
   slice.

This closes the determinant-matched permuted gradient, hence the original
terminal gradient, without any torus classification.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Under strictly positive terminal weights, any fixed determinant-matching
permuted gradient is injective. -/
theorem positiveTerminalFace_permutedGradient_injective
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
    Function.Injective
      (terminalPermutedGradientEval π F) := by
  intro p q hpq
  have hcoord :
      ∀ n : ℕ,
        ∀ i : Fin 4,
          (lambda i).natAbs = n ->
            p i = q i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      let t : ℤ := lambda i
      let v : Fin 4 -> K :=
        terminalWeightSliceDifference
          lambda t p q
      have hlow :
          ∀ j : Fin 4,
            lambda j < t ->
              p j = q j := by
        intro j hj
        have habs :
            (lambda j).natAbs < n := by
          rw [← hi]
          exact
            Int.natAbs_lt_natAbs_of_nonneg_of_lt
              (le_of_lt (hpos j)) hj
        exact ih (lambda j).natAbs habs j rfl
      have hsupp :
          IsSupportedOnTerminalWeight
            lambda t v := by
        dsimp [v]
        exact
          terminalWeightSliceDifference_supported
            lambda t p q
      have hblock :
          ∀ k : Fin 4,
            lambda k = t ->
              Matrix.vecMul v
                (terminalPermutedHessianMatrix
                  π F) k = 0 := by
        intro k hk
        have hlowk :
            ∀ j : Fin 4,
              lambda j < lambda k ->
                p j = q j := by
          intro j hj
          apply hlow j
          simpa [hk] using hj
        have heval :=
          terminalPermutedGradient_eval_sub_eq_vecMul
            hface hπ hpos p q k hlowk
        have hout :
            terminalPermutedGradientEval π F p k =
              terminalPermutedGradientEval π F q k :=
          congrFun hpq k
        have hfull :
            Matrix.vecMul
                (terminalPointDifference p q)
                (terminalPermutedHessianMatrix
                  π F) k = 0 := by
          rw [← heval]
          rw [hout]
          simp
        have hslice :=
          terminalPointDifference_vecMul_eq_weightSlice
            hface hπ p q hk
        dsimp [v]
        rw [← hslice]
        exact hfull
      have hvzero :
          v = 0 :=
        terminalPermutedHessian_weightBlock_kernel_zero
          hface hπ hsupp hblock
      have hvi :=
        congrFun hvzero i
      have hdiff :
          p i - q i = 0 := by
        simpa [v, t,
          terminalWeightSliceDifference] using hvi
      exact sub_eq_zero.mp hdiff
  funext i
  exact hcoord (lambda i).natAbs i rfl

/-- The original terminal gradient is injective whenever every terminal
weight is strictly positive. -/
theorem positiveTerminalFace_gradient_injective
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda) :
    Function.Injective (mvGradientMap F) := by
  rcases
      nonScalarTerminalConformalFace_has_complementWeightPermutation
        hface with
    ⟨π, hπ⟩
  exact
    mvGradientMap_injective_of_permuted
      π F
      (positiveTerminalFace_permutedGradient_injective
        hface hπ hpos)

/-- **Closed strictly-positive endpoint.**
A distinct exact terminal gradient collision cannot survive the `k = 0`
branch. -/
theorem positiveTerminalFace_collision_impossible
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hpos :
      HasStrictlyPositiveTerminalWeights lambda)
    (p q : Fin 4 -> K)
    (hpq : p ≠ q)
    (hcoll :
      HasExactGradientCollision F p q) :
    False := by
  exact
    exactGradientCollision_impossible_of_injective
      F p q hpq
      (positiveTerminalFace_gradient_injective
        hface hpos)
      hcoll

end

end HC4.Newton
