import HC4.Valuation.AdaptiveAlignedSmithFamilyHessianFourBlock
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import HC4.Valuation.ZeroGradientNormalization
import HC4.Valuation.MovingCollisionRecentering
import Mathlib.Tactic

/-!
# Recentered adaptive blocker Hessian four-block

The canonical blocker geometry is expressed on the right-recentered special
fibre

    longitudinalRightRecenterHom E.rawSpecialFiber,

whereas `AdaptiveAlignedSmithFamilyHessianFourBlock` constructs its honest
Hessian block on the unrecentered endpoint family `E.family`.

This file removes that final representation mismatch without introducing any
new geometry.  Translate the *actual polynomial family* by its retained right
moving section.  Because that section specializes to `e₀`, the special fibre
of the translated family is exactly the longitudinal right recentering already
used by the blocker lemmas.  Translation preserves the exact Hessian defect.

We then move the family parameter to the outer polynomial ring exactly as in
`AdaptiveAlignedSmithFamilyHessianFourBlock`, allow an arbitrary simultaneous
coordinate permutation, and package the resulting symmetric matrix as a
`GeneralFourBlock`.

For every coordinate permutation `rho` the determinant clock remains

    determinantCore = X ^ E.defect.

Thus the next genuinely geometric theorem is finite: choose a chart/permutation
from the blocker pattern and prove the constant active minor / rank-one Schur
shape on this recentered special fibre.  No determinant transport or family
recentring remains in that theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u

variable {K : Type u} [Field K]

/-! ## Honest family-level right recentering -/

/-- Translate the actual endpoint family by its retained right moving section.
At the special parameter this is the affine recentering `old x = new x + 1`
used throughout the blocker analysis. -/
noncomputable def AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  polynomialFamilyTranslationHom (K := K) E.movingSection E.family

/-- The special fibre of the honest family-level recentering is literally the
right-recentered special fibre used by the blocker competition. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily_specialFiber
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    polynomialFamilySpecialFiber E.rightRecenteredFamily =
      longitudinalRightRecenterHom (K := K) E.rawSpecialFiber := by
  unfold AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily
  simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using
    (polynomialFamilySpecialFiber_translation_eq_longitudinalRightRecenter
      (K := K) E.movingSection E.sectionSpecial E.family)

/-- Source translation preserves the exact pure Hessian determinant clock. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily_hessianDefect
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    HasPolynomialFamilyHessianDefect
      (K := K) E.rightRecenteredFamily E.defect := by
  unfold AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily
  exact
    polynomialFamilyTranslationHom_preservesHessianDefect
      E.movingSection E.family E.hessianDefect

/-! ## Recentered polynomial-series Hessian -/

/-- Honest Hessian of the right-recentered endpoint family, with the family
parameter moved to the outer polynomial ring. -/
noncomputable def adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (polynomialFamilySeriesHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian E.rightRecenteredFamily)

/-- The recentered polynomial-series Hessian is symmetric. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_symmetric
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    ∀ i j,
      adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E i j =
        adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E j i := by
  intro i j
  unfold adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix
  change
    polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian E.rightRecenteredFamily i j) =
      polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian E.rightRecenteredFamily j i)
  apply congrArg (polynomialFamilySeriesHom (K := K))
  change
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i E.rightRecenteredFamily) =
      MvPolynomial.pderiv i
        (MvPolynomial.pderiv j E.rightRecenteredFamily)
  rw [pderiv_comm_commRing]

/-! ## Permutation-aware four-block -/

/-- Simultaneously permute rows and columns of the recentered Hessian and
package the result as a `2+2` four-block.  Keeping the permutation explicit
lets the blocker calculation choose its natural active pair. -/
noncomputable def adaptiveAlignedEndpointRightRecenteredHessianFourBlock
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E).submatrix
      rho rho)

/-- The displayed four-block matrix is exactly the simultaneously permuted
recentered Hessian series. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianFourBlock_matrix
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).matrix =
      (adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E).submatrix
        rho rho := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact
    adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix_symmetric
      E (rho i) (rho j)

/-- **Exact recentered Hessian clock in every coordinate chart.**

The source translation and simultaneous coordinate permutation are both
lossless for the determinant.  Hence every chart of the honest recentered
Hessian still closes at exactly `E.defect`. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).determinantCore =
      Polynomial.X ^ E.defect := by
  calc
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).determinantCore =
        (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).matrix.det :=
      (GeneralFourBlock.matrix_det
        (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E)).symm
    _ =
        ((adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E).submatrix
          rho rho).det := by
      rw [adaptiveAlignedEndpointRightRecenteredHessianFourBlock_matrix]
    _ = (adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix E).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = Polynomial.X ^ E.defect := by
      unfold adaptiveAlignedEndpointRightRecenteredHessianSeriesMatrix
      rw [←
        (polynomialFamilySeriesHom (K := K)).map_det
          (HC4.Polynomial.hessian E.rightRecenteredFamily)]
      change
        polynomialFamilySeriesHom
            (K := K)
            (HC4.Polynomial.hessianDeterminant E.rightRecenteredFamily) =
          Polynomial.X ^ E.defect
      rw [E.rightRecenteredFamily_hessianDefect]
      exact polynomialFamilySeriesHom_C_X_pow E.defect

/-! ## Blocker seam -/

/-- The now-green blocker first-departure theorem is a statement about the
special fibre of the *same honest recentered family* whose Hessian block is
constructed above.  This is the representation seam needed by the finite
Hessian/Schur chart calculation. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.firstLongitudinalDeparture_on_rightRecenteredFamily
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (polynomialFamilySpecialFiber
        B.aligned.endpoint.rightRecenteredFamily)
      B.exponent := by
  rw [B.aligned.endpoint.rightRecenteredFamily_specialFiber]
  exact B.firstLongitudinalDeparture

/-- Blocker-facing exact determinant clock for any chosen recentered Hessian
chart.  The only missing facts after this theorem are finite constant-fibre
chart facts. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFourBlock_determinantCore
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (rho : Equiv.Perm (Fin 4)) :
    (adaptiveAlignedEndpointRightRecenteredHessianFourBlock
      rho B.aligned.endpoint).determinantCore =
      Polynomial.X ^ B.aligned.endpoint.defect := by
  exact
    adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
      rho B.aligned.endpoint

end

end HC4.Valuation
