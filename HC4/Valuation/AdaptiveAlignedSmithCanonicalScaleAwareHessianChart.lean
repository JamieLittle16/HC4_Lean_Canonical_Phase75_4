import HC4.Valuation.AdaptiveAlignedSmithCanonicalPacketRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# A18.4.82: exact Hessian four-block on an arbitrary scale-aware state

The existing honest four-block construction is indexed by an aligned minimal
endpoint.  The final finite-rank assembly now carries several equally honest
states which arise after presentations, Smith exposure, or saturated kernel
opening.  Their common data are already exactly those stored by
`ScaleAwareAdaptiveGeometricRestartState`:

* a polynomial family over `K[tau]`;
* an exact pure Hessian determinant clock; and
* the true absolute parameter scale.

This file moves the family parameter outside the source polynomial ring, as in
the already-green aligned endpoint construction, and packages any simultaneous
coordinate permutation of the genuine Hessian as a `GeneralFourBlock`.
Its determinant is literally `X ^ rawDefect`.

The resulting `ActualRankTwoHessianChart` carries one concrete nonzero active
`2 x 2` special-fibre minor.  No repair-state interpretation is built into the
chart; it is a purely geometric object suitable for the rank-two consumer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u
variable {K : Type u} [Field K]

/-- Honest Hessian polynomial series of an arbitrary scale-aware state. -/
noncomputable def scaleAwareHessianSeriesMatrix
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (polynomialFamilySeriesHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian s.family)

/-- Symmetry survives coefficient swapping. -/
theorem scaleAwareHessianSeriesMatrix_symmetric
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    ∀ i j,
      scaleAwareHessianSeriesMatrix s i j =
        scaleAwareHessianSeriesMatrix s j i := by
  intro i j
  unfold scaleAwareHessianSeriesMatrix
  change
    polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian s.family i j) =
      polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian s.family j i)
  apply congrArg (polynomialFamilySeriesHom (K := K))
  change
    MvPolynomial.pderiv j (MvPolynomial.pderiv i s.family) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j s.family)
  rw [pderiv_comm_commRing]

/-- Permutation-aware genuine Hessian four-block of a scale-aware state. -/
noncomputable def scaleAwareHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((scaleAwareHessianSeriesMatrix s).submatrix rho rho)

/-- The displayed matrix is exactly the simultaneously permuted Hessian
series. -/
theorem scaleAwareHessianFourBlock_matrix
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareHessianFourBlock rho s).matrix =
      (scaleAwareHessianSeriesMatrix s).submatrix rho rho := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact scaleAwareHessianSeriesMatrix_symmetric s (rho i) (rho j)

/-- **Exact determinant clock in every coordinate chart.** -/
theorem scaleAwareHessianFourBlock_determinantCore
    (rho : Equiv.Perm (Fin 4))
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    (scaleAwareHessianFourBlock rho s).determinantCore =
      Polynomial.X ^ s.rawDefect := by
  calc
    (scaleAwareHessianFourBlock rho s).determinantCore =
        (scaleAwareHessianFourBlock rho s).matrix.det :=
      (GeneralFourBlock.matrix_det (scaleAwareHessianFourBlock rho s)).symm
    _ = ((scaleAwareHessianSeriesMatrix s).submatrix rho rho).det := by
      rw [scaleAwareHessianFourBlock_matrix]
    _ = (scaleAwareHessianSeriesMatrix s).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = Polynomial.X ^ s.rawDefect := by
      unfold scaleAwareHessianSeriesMatrix
      rw [←
        (polynomialFamilySeriesHom (K := K)).map_det
          (HC4.Polynomial.hessian s.family)]
      change
        polynomialFamilySeriesHom
            (K := K) (HC4.Polynomial.hessianDeterminant s.family) =
          Polynomial.X ^ s.rawDefect
      rw [s.hessianDefect]
      exact polynomialFamilySeriesHom_C_X_pow s.rawDefect

/-- An actual rank-two Hessian chart is nothing more and nothing less than a
coordinate permutation whose active `2 x 2` determinant has nonzero constant
coefficient.  This is deliberately independent of the finite repair tag. -/
structure AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  permutation : Equiv.Perm (Fin 4)
  activeDet_coeff_zero_ne_zero :
    (scaleAwareHessianFourBlock permutation s).activeDet.coeff 0 ≠ 0

namespace AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart

/-- Exact full determinant clock of the retained chart. -/
theorem fullDet
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s) :
    (scaleAwareHessianFourBlock C.permutation s).determinantCore =
      Polynomial.X ^ s.rawDefect :=
  scaleAwareHessianFourBlock_determinantCore C.permutation s

end AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart

end

end HC4.Valuation
