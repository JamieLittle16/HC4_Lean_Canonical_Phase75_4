import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticCoreCollision
import HC4.Valuation.QuadraticFamilyCollision
import Mathlib.Tactic

/-!
# G23: nondegenerate quadratic core of the quartic final seam

G21--G22 reduce the degree-four final seam to

    F = q2 + h3 + h4,

where q2, h3 and h4 are ordinary homogeneous of degrees 2, 3 and 4,
respectively, the full Hessian determinant is exactly one, and F carries a
nontrivial antipodal gradient collision.

At the source origin, every Hessian entry of a homogeneous polynomial of
degree at least three vanishes.  Therefore the origin Hessian of F is exactly
the constant Hessian of q2.  Since det Hess(F) = 1 identically, evaluation at
the origin gives

    det Hess(q2) = 1.

Thus the quartic endgame has a genuinely nondegenerate quadratic base.  This
is the fixed linear part against which the cubic and quartic homogeneous
corrections must cancel.

No JC2 input or terminal-weight extraction is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Every Hessian entry of a positive-degree-after-two homogeneous polynomial
vanishes at the source origin. -/
theorem homogeneous_ge_three_hessian_eval_zero
    {H : MvPolynomial (Fin 4) K}
    {D : ℕ}
    (hhom : H.IsHomogeneous D)
    (hD : 3 ≤ D)
    (i j : Fin 4) :
    MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
      (HC4.Polynomial.hessian H i j) = 0 := by
  rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
  change
    MvPolynomial.coeff 0
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i H)) = 0
  have hfirst :
      (MvPolynomial.pderiv i H).IsHomogeneous (D - 1) := by
    exact hhom.pderiv
  have hsecondRaw :
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i H)).IsHomogeneous
        ((D - 1) - 1) := by
    exact hfirst.pderiv
  have hsecond :
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i H)).IsHomogeneous
        (D - 2) := by
    convert hsecondRaw using 1 <;> omega
  have hpositive : 0 < D - 2 := by
    omega
  have hdegree :
      Finsupp.degree (0 : Fin 4 →₀ ℕ) ≠ D - 2 := by
    simpa using (ne_of_lt hpositive)
  exact hsecond.coeff_eq_zero hdegree

/-- Equivalently, the constant source Hessian matrix of a degree-at-least-three
homogeneous polynomial vanishes. -/
theorem homogeneous_ge_three_quadraticFamilyHessianMatrix_eq_zero_field
    {H : MvPolynomial (Fin 4) K}
    {D : ℕ}
    (hhom : H.IsHomogeneous D)
    (hD : 3 ≤ D) :
    quadraticFamilyHessianMatrix H = 0 := by
  ext i j
  unfold quadraticFamilyHessianMatrix
  rw [MvPolynomial.constantCoeff_eq]
  have h :=
    homogeneous_ge_three_hessian_eval_zero
      (K := K) hhom hD i j
  rw [MvPolynomial.eval_zero'] at h
  simpa [HC4.Polynomial.hessian_apply] using h

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The constant source Hessian matrix of the quartic homogeneous core is
exactly the Hessian matrix of its quadratic component. -/
theorem FinalSeamQuarticHomogeneousCoreData.quadraticHessianMatrix_eq_core
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticHomogeneousCoreData) :
    quadraticFamilyHessianMatrix (C.q2 + C.h3 + C.h4) =
      quadraticFamilyHessianMatrix C.q2 := by
  have h3zero :
      quadraticFamilyHessianMatrix C.h3 = 0 :=
    homogeneous_ge_three_quadraticFamilyHessianMatrix_eq_zero_field
      (K := K) C.h3_homogeneous (by omega)
  have h4zero :
      quadraticFamilyHessianMatrix C.h4 = 0 :=
    homogeneous_ge_three_quadraticFamilyHessianMatrix_eq_zero_field
      (K := K) C.h4_homogeneous (by omega)
  ext i j
  have h3ij := congrArg (fun M => M i j) h3zero
  have h4ij := congrArg (fun M => M i j) h4zero
  simp only [quadraticFamilyHessianMatrix, Matrix.zero_apply] at h3ij h4ij ⊢
  simp only [map_add]
  rw [h3ij, h4ij]
  simp

/-- **Nondegenerate quadratic base.**

The quadratic homogeneous component of every quartic final-seam core has
constant Hessian determinant exactly one. -/
theorem FinalSeamQuarticHomogeneousCoreData.q2_hessianMatrix_det_one
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticHomogeneousCoreData) :
    (quadraticFamilyHessianMatrix C.q2).det = 1 := by
  have hcore :
      (quadraticFamilyHessianMatrix (C.q2 + C.h3 + C.h4)).det = 1 := by
    rw [quadraticFamilyHessianMatrix_det]
    rw [C.hessianDet_one]
    simp
  rw [C.quadraticHessianMatrix_eq_core] at hcore
  exact hcore

/-- In particular the quadratic Hessian matrix is invertible. -/
theorem FinalSeamQuarticHomogeneousCoreData.q2_hessianMatrix_isUnit
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticHomogeneousCoreData) :
    IsUnit (quadraticFamilyHessianMatrix C.q2) := by
  rw [Matrix.isUnit_iff_isUnit_det, C.q2_hessianMatrix_det_one]
  exact isUnit_one

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
