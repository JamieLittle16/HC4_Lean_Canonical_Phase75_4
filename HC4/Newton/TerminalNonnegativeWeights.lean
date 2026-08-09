import HC4.Newton.TerminalWeightPermutation
import Mathlib.Tactic

/-!
# Nonnegative terminal lattice weights

The terminal weights coming from a Smith-normal-form lattice inclusion are
expected to be nonnegative.  This file records the elementary consequences
of that additional geometric input.

For a non-scalar terminal conformal face with nonnegative integral weights:

* the common weighted degree is strictly positive;
* every coordinate weight lies in `[0,d]`;
* a zero-weight coordinate is paired by the determinant matching with a
  coordinate of weight exactly `d`;
* either every weight is strictly positive, or the terminal fibre lies on
  a genuine zero-weight boundary.

These facts are deliberately separated from the later endpoint theorem so
the final restart adapter only has to prove nonnegativity of the Smith
lattice exponents.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

def IsNonnegativeIntegralWeight
    (lambda : Fin 4 -> ℤ) : Prop :=
  ∀ i : Fin 4, 0 ≤ lambda i

def HasTerminalZeroWeight
    (lambda : Fin 4 -> ℤ) : Prop :=
  ∃ i : Fin 4, lambda i = 0

def HasStrictlyPositiveTerminalWeights
    (lambda : Fin 4 -> ℤ) : Prop :=
  ∀ i : Fin 4, 0 < lambda i

/-- A non-scalar weight cannot be identically zero. -/
theorem nonScalarIntegralWeight_isNontrivial
    {lambda : Fin 4 -> ℤ}
    (hnonscalar :
      IsNonScalarIntegralWeight lambda) :
    IsNontrivialIntegralWeight lambda := by
  by_contra htriv
  have hallzero :
      ∀ i : Fin 4, lambda i = 0 := by
    intro i
    by_contra hi
    apply htriv
    exact ⟨i, hi⟩
  apply hnonscalar
  exact ⟨0, hallzero⟩

/-- Under nonnegative lattice weights, the terminal weighted degree is
strictly positive. -/
theorem nonnegative_nonScalar_terminal_degree_pos
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda) :
    0 < d := by
  rcases
      nonScalarIntegralWeight_isNontrivial
        hface.2.1 with
    ⟨r, hr⟩
  have hrpos : 0 < lambda r := by
    have hrnonneg := hnonneg r
    omega
  rcases
      nondegenerateTerminalActualHessian_row_has_quadraticPartner
        hface.2.2.1 r with
    ⟨c, hcoeff⟩
  have hsum :
      lambda r + lambda c = d :=
    hface.2.2.2.2 r c hcoeff
  have hcnonneg := hnonneg c
  linarith

/-- Every terminal coordinate weight is bounded above by the common
weighted degree. -/
theorem nonnegative_terminal_weight_le_degree
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (i : Fin 4) :
    lambda i ≤ d := by
  rcases
      nondegenerateTerminalActualHessian_row_has_quadraticPartner
        hface.2.2.1 i with
    ⟨j, hcoeff⟩
  have hsum :
      lambda i + lambda j = d :=
    hface.2.2.2.2 i j hcoeff
  have hj := hnonneg j
  linarith

/-- A zero-weight coordinate is sent by every complement-matching
permutation to a degree-`d` coordinate. -/
theorem complementPermutation_zero_maps_to_degree
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {π : Equiv.Perm (Fin 4)}
    (hπ :
      ∀ i : Fin 4,
        lambda (π i) + lambda i = d)
    {i : Fin 4}
    (hi : lambda i = 0) :
    lambda (π i) = d := by
  have h := hπ i
  linarith

/-- Nonnegative terminal weights split into the strictly-positive interior
or a zero-weight boundary. -/
theorem nonnegative_terminal_positive_or_zero_boundary
    {lambda : Fin 4 -> ℤ}
    (hnonneg :
      IsNonnegativeIntegralWeight lambda) :
    HasStrictlyPositiveTerminalWeights lambda ∨
      HasTerminalZeroWeight lambda := by
  classical
  by_cases hz :
      ∃ i : Fin 4, lambda i = 0
  · exact Or.inr hz
  · left
    intro i
    have hle := hnonneg i
    have hne : lambda i ≠ 0 := by
      intro hi
      exact hz ⟨i, hi⟩
    omega

/-- Packaged residual terminal split after the Smith-lattice nonnegativity
input is supplied. -/
theorem residualTerminal_nonnegative_positive_or_zero
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hres :
      HasResidualNonScalarTerminalJump
        lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda) :
    HasStrictlyPositiveTerminalWeights lambda ∨
      HasTerminalZeroWeight lambda :=
  nonnegative_terminal_positive_or_zero_boundary hnonneg

end

end HC4.Newton
