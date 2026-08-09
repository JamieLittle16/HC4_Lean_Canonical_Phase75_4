import HC4.Newton.TerminalPositiveWeightTriangularReduction
import HC4.Newton.TerminalScalarGradient
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Linear blocks of the positive terminal permuted gradient

For a determinant-matching permutation `π`, the permuted gradient is

    G_i = pderiv (π i) F.

Its linear coefficient matrix is the actual Hessian at the origin with
output columns permuted:

    L[j,i] = Hess(F)(0)[j, π i].

This module records three facts.

1. `L` is globally injective whenever the terminal actual Hessian is
   nondegenerate.
2. Conformality forces `L[j,i] = 0` unless
   `lambda j = lambda i`.
3. Consequently every equal-weight diagonal block has trivial kernel.
   This is obtained without computing any subdeterminants: a vector
   supported on one weight level whose corresponding block equations vanish
   lies in the global kernel of `L`.

This is the linear-algebra input needed for the finite positive-weight
recursion.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- Linear matrix of the determinant-matched permuted gradient.

The first index is an input variable and the second index is an output
component, matching `Matrix.vecMul`. -/
def terminalPermutedHessianMatrix
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun j i =>
    standardActualHessianMatrix F j (π i)

/-- Row-vector multiplication by the permuted matrix is just multiplication
by the original Hessian followed by the output permutation. -/
theorem terminalPermutedHessian_vecMul_apply
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (v : Fin 4 -> K)
    (i : Fin 4) :
    Matrix.vecMul v
        (terminalPermutedHessianMatrix π F) i =
      Matrix.vecMul v
        (standardActualHessianMatrix F) (π i) := by
  rfl

/-- Nondegeneracy of the actual terminal Hessian is unchanged by the
determinant-matching output permutation. -/
theorem terminalPermutedHessian_vecMul_injective
    (π : Equiv.Perm (Fin 4))
    {F : MvPolynomial (Fin 4) K}
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F) :
    Function.Injective
      (fun v : Fin 4 -> K =>
        Matrix.vecMul v
          (terminalPermutedHessianMatrix π F)) := by
  have hdetStd :
      Matrix.det
        (standardActualHessianMatrix F) ≠ 0 := by
    unfold HasNondegenerateTerminalActualHessian at hdet
    rw [terminalActualHessianMatrix_standard_eq] at hdet
    exact hdet
  have hStd :
      Function.Injective
        (fun v : Fin 4 -> K =>
          Matrix.vecMul v
            (standardActualHessianMatrix F)) :=
    standardActualHessian_vecMul_injective
      F hdetStd
  intro v w hvw
  apply hStd
  funext j
  have h :=
    congrFun hvw (π.symm j)
  simpa [terminalPermutedHessian_vecMul_apply] using h

/-- A nonzero entry of the permuted terminal Hessian connects equal
original weights. -/
theorem terminalPermutedHessian_entry_nonzero_weight_eq
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
    {j i : Fin 4}
    (hentry :
      terminalPermutedHessianMatrix π F j i ≠ 0) :
    lambda j = lambda i := by
  have hactual :
      mvHessianComponentAt
          (fun _ => (0 : K))
          F j (π i) ≠ 0 := by
    simpa [terminalPermutedHessianMatrix,
      standardActualHessianMatrix] using hentry
  have hcoeff :
      MvPolynomial.coeff
        (quadraticExponent j (π i)) F ≠ 0 :=
    mvHessianComponentAt_origin_ne_zero_quadraticCoeff
      F j (π i) hactual
  have hconf :
      lambda j + lambda (π i) = d :=
    hface.2.2.2.2 j (π i) hcoeff
  have hmatch := hπ i
  linarith

/-- Cross-weight entries of the linear matrix vanish. -/
theorem terminalPermutedHessian_entry_eq_zero_of_weight_ne
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
    {j i : Fin 4}
    (hne : lambda j ≠ lambda i) :
    terminalPermutedHessianMatrix π F j i = 0 := by
  by_contra hentry
  exact hne
    (terminalPermutedHessian_entry_nonzero_weight_eq
      hface hπ hentry)

/-- A vector is supported on one terminal weight level. -/
def IsSupportedOnTerminalWeight
    (lambda : Fin 4 -> ℤ)
    (t : ℤ)
    (v : Fin 4 -> K) : Prop :=
  ∀ j : Fin 4,
    lambda j ≠ t ->
      v j = 0

/-- If a vector is supported on one weight level, every output coordinate
of a different weight automatically vanishes after multiplication by the
permuted Hessian. -/
theorem terminalPermutedHessian_vecMul_eq_zero_off_weight
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
    {t : ℤ}
    {v : Fin 4 -> K}
    (hsupp :
      IsSupportedOnTerminalWeight lambda t v)
    {i : Fin 4}
    (hi : lambda i ≠ t) :
    Matrix.vecMul v
        (terminalPermutedHessianMatrix π F) i = 0 := by
  classical
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjt : lambda j = t
  · have hji : lambda j ≠ lambda i := by
      intro hEq
      apply hi
      calc
        lambda i = lambda j := hEq.symm
        _ = t := hjt
    rw [terminalPermutedHessian_entry_eq_zero_of_weight_ne
      hface hπ hji]
    simp
  · rw [hsupp j hjt]
    simp

/-- **Equal-weight block kernel is trivial.**

No subdeterminant is required.  The conformal zero pattern extends the
weight-level kernel equation to the full permuted Hessian, whose global
injectivity then kills the vector. -/
theorem terminalPermutedHessian_weightBlock_kernel_zero
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
    {t : ℤ}
    {v : Fin 4 -> K}
    (hsupp :
      IsSupportedOnTerminalWeight lambda t v)
    (hblock :
      ∀ i : Fin 4,
        lambda i = t ->
          Matrix.vecMul v
            (terminalPermutedHessianMatrix π F) i = 0) :
    v = 0 := by
  have hfull :
      Matrix.vecMul v
          (terminalPermutedHessianMatrix π F) =
        Matrix.vecMul (0 : Fin 4 -> K)
          (terminalPermutedHessianMatrix π F) := by
    funext i
    by_cases hi : lambda i = t
    · rw [hblock i hi]
      simp
    · rw [terminalPermutedHessian_vecMul_eq_zero_off_weight
        hface hπ hsupp hi]
      simp
  exact
    terminalPermutedHessian_vecMul_injective
      π hface.2.2.1 hfull

/-- Evaluating one more partial derivative at the origin extracts the
linear coefficient of a polynomial. -/
theorem eval_zero_pderiv_eq_linearCoeff
    (P : MvPolynomial (Fin 4) K)
    (j : Fin 4) :
    MvPolynomial.eval
        (fun _ => (0 : K))
        (MvPolynomial.pderiv j P) =
      MvPolynomial.coeff
        (Finsupp.single j 1) P := by
  rw [MvPolynomial.eval_zero']
  rw [MvPolynomial.constantCoeff_eq]
  have h :=
    coeff_pderiv_backport
      (K := K) j P (0 : Fin 4 →₀ ℕ)
  simpa using h

/-- The permuted Hessian entry is exactly the same-weight linear
coefficient of the corresponding permuted-gradient component. -/
theorem terminalPermutedHessian_eq_linearCoeff
    (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (j i : Fin 4) :
    terminalPermutedHessianMatrix π F j i =
      MvPolynomial.coeff
        (Finsupp.single j 1)
        (terminalPermutedGradient π F i) := by
  unfold terminalPermutedHessianMatrix
  unfold standardActualHessianMatrix
  unfold mvHessianComponentAt
  unfold terminalPermutedGradient
  exact eval_zero_pderiv_eq_linearCoeff
    (MvPolynomial.pderiv (π i) F) j

end

end HC4.Newton
