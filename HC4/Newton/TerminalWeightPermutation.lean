import HC4.Newton.TerminalDirectRankJumpReduction
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Determinant permutation pairing for terminal weights

The Phase 93.26 residual branch knows that every Hessian row has some
opposite centred-weight partner.  Nondegeneracy gives more: a nonzero
determinant has at least one nonzero Leibniz permutation term.

Along such a permutation every selected Hessian entry is nonzero.  Since
every nonzero quadratic Hessian entry joins complementary terminal weights,
the permutation itself pairs all four terminal weights.

This is the finite matching statement behind the usual conformal-hyperbolic
normal form and is useful both in the strictly-positive and zero-weight
terminal branches.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- A square 4x4 matrix with nonzero determinant has a permutation whose
entire Leibniz product is nonzero. -/
theorem matrix4_det_ne_zero_exists_permutation_entries_ne_zero
    (M : Matrix (Fin 4) (Fin 4) K)
    (hdet : Matrix.det M ≠ 0) :
    ∃ π : Equiv.Perm (Fin 4),
      ∀ i : Fin 4, M (π i) i ≠ 0 := by
  classical
  have hex :
      ∃ π : Equiv.Perm (Fin 4),
        ((↑↑(Equiv.Perm.sign π) : K) *
          ∏ i : Fin 4, M (π i) i) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hdet
    rw [Matrix.det_apply']
    apply Finset.sum_eq_zero
    intro π hπ
    exact hnone π
  rcases hex with ⟨π, hterm⟩
  have hprod :
      (∏ i : Fin 4, M (π i) i) ≠ 0 := by
    intro hp
    apply hterm
    rw [hp]
    simp
  refine ⟨π, ?_⟩
  intro i
  exact
    (Finset.prod_ne_zero_iff.mp hprod)
      i (Finset.mem_univ i)

/-- A terminal conformal face has a determinant matching permutation:
every chosen Hessian entry gives the complementary original-weight
relation `lambda_(pi i) + lambda_i = d`. -/
def HasTerminalComplementWeightPermutation
    (lambda : Fin 4 -> ℤ)
    (d : ℤ) : Prop :=
  ∃ π : Equiv.Perm (Fin 4),
    ∀ i : Fin 4,
      lambda (π i) + lambda i = d

/-- Equivalent centred formulation of the matching. -/
def HasTerminalOppositeCenteredPermutation
    (lambda : Fin 4 -> ℤ)
    (d : ℤ) : Prop :=
  ∃ π : Equiv.Perm (Fin 4),
    ∀ i : Fin 4,
      centeredTerminalWeight lambda d (π i) =
        - centeredTerminalWeight lambda d i

/-- Actual Hessian nondegeneracy plus conformality produces a global
complement-weight permutation. -/
theorem nonScalarTerminalConformalFace_has_complementWeightPermutation
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F) :
    HasTerminalComplementWeightPermutation lambda d := by
  have hdet :
      Matrix.det
        (terminalActualHessianMatrix
          (0 : Fin 4) 1 2 3 F) ≠ 0 :=
    hface.2.2.1
  rcases
      matrix4_det_ne_zero_exists_permutation_entries_ne_zero
        (terminalActualHessianMatrix
          (0 : Fin 4) 1 2 3 F)
        hdet with
    ⟨π, hentries⟩
  refine ⟨π, ?_⟩
  intro i
  have hentry :
      mvHessianComponentAt
        (fun _ => (0 : K)) F (π i) i ≠ 0 := by
    simpa only
      [terminalActualHessianMatrix,
       terminalFourCoordinate_standard] using hentries i
  have hcoeff :
      MvPolynomial.coeff
        (quadraticExponent (π i) i) F ≠ 0 :=
    mvHessianComponentAt_origin_ne_zero_quadraticCoeff
      F (π i) i hentry
  exact hface.2.2.2.2 (π i) i hcoeff

/-- The determinant matching is exactly an opposite pairing after
centering the terminal weights. -/
theorem complementWeightPermutation_to_oppositeCentered
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    (hperm :
      HasTerminalComplementWeightPermutation lambda d) :
    HasTerminalOppositeCenteredPermutation lambda d := by
  rcases hperm with ⟨π, hπ⟩
  refine ⟨π, ?_⟩
  intro i
  have h := hπ i
  unfold centeredTerminalWeight
  linarith

/-- Non-scalar terminal conformal faces therefore carry a global opposite
centred-weight permutation, not merely one opposite pair. -/
theorem nonScalarTerminalConformalFace_has_oppositeCenteredPermutation
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F) :
    HasTerminalOppositeCenteredPermutation lambda d := by
  exact
    complementWeightPermutation_to_oppositeCentered
      (nonScalarTerminalConformalFace_has_complementWeightPermutation
        hface)

end

end HC4.Newton
