import HC4.Newton.TerminalConformalWeight
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Quadratic Hessian nondegeneracy at a terminal conformal face

Phase 93.22 proves the weight-theoretic half of the terminal direct-rank
jump: once a scalar nonzero terminal weight sees any nonzero quadratic
coefficient, weighted homogeneity forces the whole terminal fibre to have
ordinary degree two.

This file supplies the complementary nondegeneracy bridge without relying
on version-sensitive second-derivative APIs.

For a polynomial `F`, define its quadratic Hessian coefficient entry by

    H_ii = 2 * [X_i^2] F,
    H_ij =     [X_i X_j] F  (i != j).

This is exactly the Hessian at the origin of the quadratic Taylor part.
Restrict it to four chosen terminal coordinates and take its 4x4
determinant.

If that determinant is nonzero, the matrix has a nonzero entry, hence `F`
has a nonzero quadratic coefficient.  Combining this witness with the
green Phase 93.22 scalar-weight theorem gives the scalar terminal
conclusion directly:

    nondegenerate quadratic Hessian
    + scalar nonzero terminal weight
    + weighted homogeneity
        ->
    pure quadratic support.

The next terminal layer can now identify this coefficient Hessian with the
actual determinant-closing Hessian supplied by the restart construction.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Hessian entry of the quadratic Taylor part at the origin, expressed
directly through coefficients. -/
noncomputable def terminalQuadraticHessianEntry
    (i j : σ)
    (F : MvPolynomial σ K) : K := by
  classical
  exact
    if i = j then
      2 * MvPolynomial.coeff (quadraticExponent i j) F
    else
      MvPolynomial.coeff (quadraticExponent i j) F

/-- Four selected terminal coordinates, indexed by `Fin 4`. -/
def terminalFourCoordinate
    (x y z w : σ) : Fin 4 -> σ :=
  Fin.cases x
    (Fin.cases y
      (Fin.cases z
        (fun _ => w)))

/-- The 4x4 Hessian of the quadratic Taylor part in four terminal
coordinates. -/
def terminalQuadraticHessianMatrix
    (x y z w : σ)
    (F : MvPolynomial σ K) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j =>
    terminalQuadraticHessianEntry
      (terminalFourCoordinate x y z w i)
      (terminalFourCoordinate x y z w j)
      F

/-- Nondegeneracy certificate for the terminal quadratic Hessian. -/
def HasNondegenerateTerminalQuadraticHessian
    (x y z w : σ)
    (F : MvPolynomial σ K) : Prop :=
  Matrix.det
    (terminalQuadraticHessianMatrix x y z w F) ≠ 0

/-- A 4x4 matrix with nonzero determinant has a nonzero entry. -/
theorem matrix4_det_ne_zero_exists_entry_ne_zero
    (M : Matrix (Fin 4) (Fin 4) K)
    (hdet : Matrix.det M ≠ 0) :
    ∃ i j : Fin 4, M i j ≠ 0 := by
  by_contra hnone
  have hall :
      ∀ i j : Fin 4, M i j = 0 := by
    intro i j
    by_contra hij
    exact hnone ⟨i, j, hij⟩
  have hM : M = 0 := by
    ext i j
    exact hall i j
  apply hdet
  rw [hM]
  simp

/-- A nonzero coefficient-Hessian entry always comes from a nonzero
quadratic coefficient.  On the diagonal this only uses the implication
`2*c != 0 -> c != 0`; no characteristic assumption is needed. -/
theorem terminalQuadraticHessianEntry_ne_zero_coeff_ne_zero
    (i j : σ)
    (F : MvPolynomial σ K)
    (hentry :
      terminalQuadraticHessianEntry i j F ≠ 0) :
    MvPolynomial.coeff (quadraticExponent i j) F ≠ 0 := by
  unfold terminalQuadraticHessianEntry at hentry
  by_cases hij : i = j
  · rw [if_pos hij] at hentry
    intro hcoeff
    apply hentry
    simp [hcoeff]
  · rw [if_neg hij] at hentry
    exact hentry

/-- A nondegenerate four-coordinate quadratic Hessian supplies the
quadratic coefficient witness required by Phase 93.22. -/
theorem nondegenerateTerminalQuadraticHessian_exists_quadraticCoeff
    (x y z w : σ)
    (F : MvPolynomial σ K)
    (hdet :
      HasNondegenerateTerminalQuadraticHessian
        x y z w F) :
    ∃ i j : σ,
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0 := by
  unfold HasNondegenerateTerminalQuadraticHessian at hdet
  rcases
      matrix4_det_ne_zero_exists_entry_ne_zero
        (terminalQuadraticHessianMatrix x y z w F)
        hdet with
    ⟨r, c, hentry⟩
  let i := terminalFourCoordinate x y z w r
  let j := terminalFourCoordinate x y z w c
  refine ⟨i, j, ?_⟩
  apply
    terminalQuadraticHessianEntry_ne_zero_coeff_ne_zero
      i j F
  exact hentry

/-- Nondegenerate terminal quadratic Hessian implies the terminal
polynomial itself is nonzero. -/
theorem nondegenerateTerminalQuadraticHessian_polynomial_ne_zero
    (x y z w : σ)
    (F : MvPolynomial σ K)
    (hdet :
      HasNondegenerateTerminalQuadraticHessian
        x y z w F) :
    F ≠ 0 := by
  rcases
      nondegenerateTerminalQuadraticHessian_exists_quadraticCoeff
        x y z w F hdet with
    ⟨i, j, hcoeff⟩
  intro hF
  subst F
  simpa using hcoeff

/-- **Scalar terminal conformal face, quadratic conclusion.**
A nondegenerate terminal quadratic Hessian removes the explicit quadratic
coefficient hypothesis from Phase 93.22. -/
theorem scalarTerminal_nondegenerate_hasPureQuadraticSupport
    (x y z w : σ)
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (ha : a ≠ 0)
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (hdet :
      HasNondegenerateTerminalQuadraticHessian
        x y z w F) :
    HasPureQuadraticSupport F := by
  rcases
      nondegenerateTerminalQuadraticHessian_exists_quadraticCoeff
        x y z w F hdet with
    ⟨i, j, hquad⟩
  exact
    scalarWeightedHomogeneous_hasPureQuadraticSupport
      ha hhom i j hquad

/-- The scalar terminal endpoint simultaneously records nontriviality and
pure quadratic support. -/
theorem scalarTerminal_nondegenerate_endpoint
    (x y z w : σ)
    {a d : ℤ}
    {F : MvPolynomial σ K}
    (ha : a ≠ 0)
    (hhom :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F)
    (hdet :
      HasNondegenerateTerminalQuadraticHessian
        x y z w F) :
    F ≠ 0 ∧ HasPureQuadraticSupport F := by
  constructor
  · exact
      nondegenerateTerminalQuadraticHessian_polynomial_ne_zero
        x y z w F hdet
  · exact
      scalarTerminal_nondegenerate_hasPureQuadraticSupport
        x y z w ha hhom hdet

end

end HC4.Newton
