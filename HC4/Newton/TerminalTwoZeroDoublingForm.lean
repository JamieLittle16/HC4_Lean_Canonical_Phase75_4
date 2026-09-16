import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Exact four-variable doubling form on the two-zero boundary

The support theorem already proves

    F = X₂ A + X₃ C

with

    A = pderiv 2 F,
    C = pderiv 3 F,

and both `A,C` depending only on the zero-weight variables `X₀,X₁`.

This module packages that statement and records the corresponding gradient
identities.  These are exactly the symbolic equations needed to identify
the terminal fibre with a planar Hessian doubling in the next phase.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

def standardTwoZeroA
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 2 F

def standardTwoZeroC
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv 3 F

/-- Formal differentiation commutes with extracting the first two-zero base
coefficient.  This is the directed normalization used by finite Hessian
arguments; unlike unfolding `standardTwoZeroA`, it does not create a simp
cycle with `standardTwoZero_pderiv_two_eq_A`. -/
@[simp] theorem pderiv_standardTwoZeroA
    (i : Fin 4)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv i (standardTwoZeroA F) =
      standardTwoZeroA (MvPolynomial.pderiv i F) := by
  simp only [standardTwoZeroA]
  rw [pderiv_comm_backport]

/-- Formal differentiation commutes with extracting the second two-zero base
coefficient. -/
@[simp] theorem pderiv_standardTwoZeroC
    (i : Fin 4)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv i (standardTwoZeroC F) =
      standardTwoZeroC (MvPolynomial.pderiv i F) := by
  simp only [standardTwoZeroC]
  rw [pderiv_comm_backport]

/-- Exact support-level doubling certificate in the ambient four-variable
ring. -/
def HasStandardTwoZeroDoublingForm
    (F : MvPolynomial (Fin 4) K) : Prop :=
  F =
      MvPolynomial.X 2 * standardTwoZeroA F +
        MvPolynomial.X 3 * standardTwoZeroC F ∧
    DependsOnlyOnStandardZeroPair
      (standardTwoZeroA F) ∧
    DependsOnlyOnStandardZeroPair
      (standardTwoZeroC F)

/-- Every positive-degree standard two-zero weighted homogeneous potential
has the exact doubling form. -/
theorem standardTwoZero_hasDoublingForm
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    HasStandardTwoZeroDoublingForm F := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [standardTwoZeroA, standardTwoZeroC] using
      (standardTwoZero_euler_decomposition
        hd hhom).symm
  · exact
      standardTwoZero_pderiv_two_zeroPairSupported
        hd hhom
  · exact
      standardTwoZero_pderiv_three_zeroPairSupported
        hd hhom

/-- Zero-coordinate derivative formula for the first base coordinate. -/
theorem standardTwoZero_pderiv_zero_formula
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    MvPolynomial.pderiv 0 F =
      MvPolynomial.X 2 *
          MvPolynomial.pderiv 0
            (standardTwoZeroA F) +
        MvPolynomial.X 3 *
          MvPolynomial.pderiv 0
            (standardTwoZeroC F) := by
  have hform :=
    standardTwoZero_hasDoublingForm hd hhom
  have hderiv :=
    congrArg
      (MvPolynomial.pderiv (R := K) 0)
      hform.1
  simpa [standardTwoZeroA, standardTwoZeroC] using hderiv

/-- Zero-coordinate derivative formula for the second base coordinate. -/
theorem standardTwoZero_pderiv_one_formula
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hd : 0 < d)
    (hhom :
      IsIntegralWeightedHomogeneous
        (standardTwoZeroTerminalWeight d) d F) :
    MvPolynomial.pderiv 1 F =
      MvPolynomial.X 2 *
          MvPolynomial.pderiv 1
            (standardTwoZeroA F) +
        MvPolynomial.X 3 *
          MvPolynomial.pderiv 1
            (standardTwoZeroC F) := by
  have hform :=
    standardTwoZero_hasDoublingForm hd hhom
  have hderiv :=
    congrArg
      (MvPolynomial.pderiv (R := K) 1)
      hform.1
  simpa [standardTwoZeroA, standardTwoZeroC] using hderiv

/-- The two positive-coordinate gradient components are exactly the two
base coefficient polynomials. -/
@[simp] theorem standardTwoZero_pderiv_two_eq_A
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 2 F =
      standardTwoZeroA F := rfl

@[simp] theorem standardTwoZero_pderiv_three_eq_C
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.pderiv 3 F =
      standardTwoZeroC F := rfl

/-- Package the exact normal form directly from the terminal conformal face
once two zero coordinates have been placed in positions `0,1`. -/
theorem nonnegativeTerminalFace_two_standard_zeros_hasDoublingForm
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0) :
    HasStandardTwoZeroDoublingForm F := by
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
  exact standardTwoZero_hasDoublingForm hd hhom

/-- The same terminal hypotheses force the full positive-positive Hessian
block to vanish. -/
theorem nonnegativeTerminalFace_two_standard_zeros_positiveHessian_zero
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (hnonneg :
      IsNonnegativeIntegralWeight lambda)
    (h0 : lambda 0 = 0)
    (h1 : lambda 1 = 0) :
    MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 2 F) = 0 ∧
      MvPolynomial.pderiv 2
        (MvPolynomial.pderiv 3 F) = 0 ∧
      MvPolynomial.pderiv 3
        (MvPolynomial.pderiv 3 F) = 0 := by
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
    standardTwoZero_positivePositiveHessian_zero
      hd hhom

end

end HC4.Newton
