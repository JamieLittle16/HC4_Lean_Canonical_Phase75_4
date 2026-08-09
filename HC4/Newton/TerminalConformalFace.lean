import HC4.Newton.TerminalActualHessian
import Mathlib.Tactic

/-!
# Terminal conformal face

Phases 93.22--93.24 formalised the two local ingredients of the terminal
direct-rank-jump argument:

* weighted homogeneity forces every nonzero quadratic coefficient
  `X_i X_j` onto the hyperplane `lambda_i + lambda_j = d`;
* a nonzero determinant of the actual Hessian at the origin supplies a
  genuine nonzero quadratic coefficient.

This file packages those facts into the exact scalar/non-scalar terminal
dichotomy required by the restart proof.

No torus endpoint theorem is invoked here.  The output is deliberately a
purely local certificate:

* scalar nontrivial terminal weight  -> the fibre has pure quadratic support;
* non-scalar terminal weight         -> the fibre has a nondegenerate actual
  Hessian and an explicit conformal quadratic weight condition.

The next terminal-direct-rank-jump module may therefore dispatch the
non-scalar certificate to the existing exact conformal-torus endpoint
classification without hiding any extra geometric assumption in this file.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- An integral source weight is scalar when all coordinates have one
common integer weight. -/
def IsScalarIntegralWeight
    (lambda : σ -> ℤ) : Prop :=
  ∃ a : ℤ, ∀ i : σ, lambda i = a

/-- A genuinely anisotropic integral source weight. -/
def IsNonScalarIntegralWeight
    (lambda : σ -> ℤ) : Prop :=
  ¬ IsScalarIntegralWeight lambda

/-- The terminal source weight is nontrivial. -/
def IsNontrivialIntegralWeight
    (lambda : σ -> ℤ) : Prop :=
  ∃ i : σ, lambda i ≠ 0

/-- Conformality of the quadratic support for an integral weight:
every nonzero quadratic coefficient has the common weight sum `d`. -/
def HasConformalQuadraticWeight
    (lambda : σ -> ℤ)
    (d : ℤ)
    (F : MvPolynomial σ K) : Prop :=
  ∀ i j : σ,
    MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0 ->
      lambda i + lambda j = d

/-- Weighted homogeneity already implies conformality on every nonzero
quadratic coefficient. -/
theorem weightedHomogeneous_hasConformalQuadraticWeight
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F) :
    HasConformalQuadraticWeight lambda d F := by
  intro i j hcoeff
  exact
    weightedHomogeneous_quadraticCoeff_weightSum
      hhom i j hcoeff

/-- The actual determinant-closing Hessian plus weighted homogeneity gives
a nonzero terminal fibre carrying the conformal quadratic weight
certificate. -/
theorem terminalActualHessian_hasConformalQuadraticWeight
    (x y z w : σ)
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    F ≠ 0 ∧
      HasConformalQuadraticWeight lambda d F := by
  constructor
  · exact
      nondegenerateTerminalActualHessian_polynomial_ne_zero
        x y z w F hdet
  · exact
      weightedHomogeneous_hasConformalQuadraticWeight
        hhom

/-- In the scalar case, nontriviality of the source weight turns the
common scalar into a nonzero integer, so the green Phase 93.24 scalar
terminal theorem applies. -/
theorem scalarTerminal_actualHessian_endpoint_of_scalarWeight
    (x y z w : σ)
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hscalar :
      IsScalarIntegralWeight lambda)
    (hnontrivial :
      IsNontrivialIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    F ≠ 0 ∧ HasPureQuadraticSupport F := by
  rcases hscalar with ⟨a, ha⟩
  have hlambda :
      lambda = (fun _ : σ => a) := by
    funext i
    exact ha i
  have ha0 : a ≠ 0 := by
    rcases hnontrivial with ⟨i, hi⟩
    rw [hlambda] at hi
    exact hi
  have hhomScalar :
      IsIntegralWeightedHomogeneous
        (fun _ : σ => a) d F := by
    simpa [hlambda] using hhom
  exact
    scalarTerminal_actualHessian_nondegenerate_endpoint
      x y z w
      ha0 hhomScalar hdet

/-- Packaged certificate for a genuinely non-scalar terminal conformal
face. -/
def HasNonScalarTerminalConformalFace
    (x y z w : σ)
    (lambda : σ -> ℤ)
    (d : ℤ)
    (F : MvPolynomial σ K) : Prop :=
  F ≠ 0 ∧
  IsNonScalarIntegralWeight lambda ∧
  HasNondegenerateTerminalActualHessian x y z w F ∧
  IsIntegralWeightedHomogeneous lambda d F ∧
  HasConformalQuadraticWeight lambda d F

/-- The non-scalar branch is an explicit conformal terminal certificate,
with no endpoint theorem assumed. -/
theorem nonScalarTerminal_actualHessian_conformalFace
    (x y z w : σ)
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hnonscalar :
      IsNonScalarIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    HasNonScalarTerminalConformalFace
      x y z w lambda d F := by
  refine
    ⟨nondegenerateTerminalActualHessian_polynomial_ne_zero
        x y z w F hdet,
     hnonscalar,
     hdet,
     hhom,
     ?_⟩
  exact
    weightedHomogeneous_hasConformalQuadraticWeight
      hhom

/-- The exact local output of `TerminalConformalFace`:
a nontrivial terminal weight is either scalar, forcing a purely quadratic
fibre, or genuinely non-scalar and conformal on its nondegenerate quadratic
part. -/
theorem terminalConformalFace_dichotomy
    (x y z w : σ)
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hnontrivial :
      IsNontrivialIntegralWeight lambda)
    (hhom :
      IsIntegralWeightedHomogeneous lambda d F)
    (hdet :
      HasNondegenerateTerminalActualHessian
        x y z w F) :
    (F ≠ 0 ∧ HasPureQuadraticSupport F) ∨
      HasNonScalarTerminalConformalFace
        x y z w lambda d F := by
  classical
  by_cases hscalar :
      IsScalarIntegralWeight lambda
  · exact
      Or.inl
        (scalarTerminal_actualHessian_endpoint_of_scalarWeight
          x y z w
          hscalar hnontrivial hhom hdet)
  · exact
      Or.inr
        (nonScalarTerminal_actualHessian_conformalFace
          x y z w
          hscalar hhom hdet)

/-- The non-scalar terminal certificate explicitly contains a genuine
quadratic coefficient and its conformal weight equation. -/
theorem nonScalarTerminalConformalFace_exists_weightedQuadraticCoeff
    (x y z w : σ)
    {lambda : σ -> ℤ}
    {d : ℤ}
    {F : MvPolynomial σ K}
    (hface :
      HasNonScalarTerminalConformalFace
        x y z w lambda d F) :
    ∃ i j : σ,
      MvPolynomial.coeff
          (quadraticExponent i j) F ≠ 0 ∧
        lambda i + lambda j = d := by
  rcases
      nondegenerateTerminalActualHessian_exists_quadraticCoeff
        x y z w F hface.2.2.1 with
    ⟨i, j, hcoeff⟩
  refine ⟨i, j, hcoeff, ?_⟩
  exact hface.2.2.2.2 i j hcoeff

end

end HC4.Newton
