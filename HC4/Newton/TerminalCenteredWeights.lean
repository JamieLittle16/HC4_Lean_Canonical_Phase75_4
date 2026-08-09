import HC4.Newton.TerminalConformalFace
import Mathlib.Tactic

/-!
# Centred terminal weights

For a terminal conformal face of weighted degree `d`, set

    mu_i = 2 * lambda_i - d.

Whenever the quadratic coefficient `X_i X_j` is nonzero, conformality gives

    mu_i + mu_j = 0.

A nondegenerate actual Hessian has a nonzero entry in every row.  Therefore
every coordinate has an opposite centred-weight partner.

In the genuinely non-scalar four-variable branch, not all centred weights
can vanish.  Hence there is a distinct pair of coordinates carrying
nonzero opposite centred weights.

This is the first structural reduction of the non-scalar terminal endpoint:
instead of an arbitrary conformal weight, the remaining branch carries an
explicit nonzero opposite-weight pair.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The centred integral weight attached to weighted degree `d`. -/
def centeredTerminalWeight
    (lambda : Fin 4 -> ℤ)
    (d : ℤ)
    (i : Fin 4) : ℤ :=
  2 * lambda i - d

/-- A conformal quadratic coefficient joins opposite centred weights. -/
theorem conformalQuadraticCoeff_centered_sum_zero
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hconf :
      HasConformalQuadraticWeight lambda d F)
    {i j : Fin 4}
    (hcoeff :
      MvPolynomial.coeff
        (quadraticExponent i j) F ≠ 0) :
    centeredTerminalWeight lambda d i +
        centeredTerminalWeight lambda d j = 0 := by
  have hsum :
      lambda i + lambda j = d :=
    hconf i j hcoeff
  unfold centeredTerminalWeight
  linarith

/-- Every row of a square matrix with nonzero determinant has a nonzero
entry. -/
theorem matrix4_det_ne_zero_row_exists_entry
    (M : Matrix (Fin 4) (Fin 4) K)
    (hdet : Matrix.det M ≠ 0)
    (r : Fin 4) :
    ∃ c : Fin 4, M r c ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hdet
  exact Matrix.det_eq_zero_of_row_eq_zero r hnone

/-- In the standard `Fin 4` chart, the terminal coordinate enumeration
is the identity. -/
@[simp] theorem terminalFourCoordinate_standard
    (r : Fin 4) :
    terminalFourCoordinate
        (0 : Fin 4) 1 2 3 r = r := by
  fin_cases r <;> rfl

/-- Every coordinate of a nondegenerate terminal Hessian has a quadratic
partner with a nonzero coefficient. -/
theorem nondegenerateTerminalActualHessian_row_has_quadraticPartner
    {F : MvPolynomial (Fin 4) K}
    (hdet :
      HasNondegenerateTerminalActualHessian
        (0 : Fin 4) 1 2 3 F)
    (r : Fin 4) :
    ∃ c : Fin 4,
      MvPolynomial.coeff
        (quadraticExponent r c) F ≠ 0 := by
  have hmatrixDet :
      Matrix.det
        (terminalActualHessianMatrix
          (0 : Fin 4) 1 2 3 F) ≠ 0 := hdet
  rcases
      matrix4_det_ne_zero_row_exists_entry
        (terminalActualHessianMatrix
          (0 : Fin 4) 1 2 3 F)
        hmatrixDet r with
    ⟨c, hentry⟩
  refine ⟨c, ?_⟩
  apply
    mvHessianComponentAt_origin_ne_zero_quadraticCoeff
      F r c
  simpa only
    [terminalActualHessianMatrix,
     terminalFourCoordinate_standard] using hentry

/-- Every coordinate of a non-scalar conformal terminal face has an
opposite centred-weight partner. -/
theorem nonScalarTerminalConformalFace_centered_partner
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F)
    (r : Fin 4) :
    ∃ c : Fin 4,
      centeredTerminalWeight lambda d c =
        - centeredTerminalWeight lambda d r := by
  rcases
      nondegenerateTerminalActualHessian_row_has_quadraticPartner
        hface.2.2.1 r with
    ⟨c, hcoeff⟩
  have hzero :=
    conformalQuadraticCoeff_centered_sum_zero
      hface.2.2.2.2 hcoeff
  refine ⟨c, ?_⟩
  linarith

/-- If every centred weight vanished, the original weight would be scalar.
Therefore a non-scalar weight has a nonzero centred coordinate. -/
theorem nonScalarIntegralWeight_exists_centered_ne_zero
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    (hnonscalar :
      IsNonScalarIntegralWeight lambda) :
    ∃ r : Fin 4,
      centeredTerminalWeight lambda d r ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hnonscalar
  refine ⟨lambda 0, ?_⟩
  intro i
  have hi := hnone i
  have h0 := hnone 0
  unfold centeredTerminalWeight at hi h0
  linarith

/-- **Opposite-pair reduction.**
A genuinely non-scalar conformal terminal face with nondegenerate Hessian
contains two distinct coordinates carrying nonzero opposite centred
weights. -/
theorem nonScalarTerminalConformalFace_exists_nonzero_opposite_pair
    {lambda : Fin 4 -> ℤ}
    {d : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hface :
      HasNonScalarTerminalConformalFace
        (0 : Fin 4) 1 2 3 lambda d F) :
    ∃ r c : Fin 4,
      centeredTerminalWeight lambda d r ≠ 0 ∧
      centeredTerminalWeight lambda d c =
        - centeredTerminalWeight lambda d r ∧
      r ≠ c := by
  rcases
      nonScalarIntegralWeight_exists_centered_ne_zero
        hface.2.1 with
    ⟨r, hr⟩
  rcases
      nonScalarTerminalConformalFace_centered_partner
        hface r with
    ⟨c, hc⟩
  have hrc : r ≠ c := by
    intro hEq
    subst c
    have :
        centeredTerminalWeight lambda d r =
          - centeredTerminalWeight lambda d r :=
      hc
    have hzero :
        centeredTerminalWeight lambda d r = 0 := by
      linarith
    exact hr hzero
  exact ⟨r, c, hr, hc, hrc⟩

end

end HC4.Newton
