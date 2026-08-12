import HC4.Valuation.AdaptiveAlignedSmithExactFourBlockSchur
import HC4.Valuation.ActualParameterLayer
import HC4.Polynomial.HessianDeterminant
import Mathlib.Tactic

/-!
# Honest adaptive-family Hessian four-block

This file constructs the exact polynomial-series Hessian block carried by an
`AdaptiveAlignedSmithMinimalEndpoint`.

The endpoint family is stored as

    MvPolynomial (Fin 4) (Polynomial K),

whereas the Schur machinery uses

    Polynomial (MvPolynomial (Fin 4) K).

We therefore use the canonical coefficient-swap ring homomorphism. No
coefficient data are discarded: it simply moves the family parameter outside
the source polynomial ring.

Applying this ring hom entrywise to the genuine source Hessian gives a
symmetric polynomial matrix. Its determinant is the image of the genuine
Hessian determinant by `RingHom.map_det`; the endpoint's exact defect identity

    det Hess(P) = C (X^Delta)

therefore becomes literally

    det Hseries = X^Delta.

Consequently `GeneralFourBlock.ofSymmetricMatrix Hseries` supplies the
`fullDet` field of `AdaptiveAlignedExactFourBlockSchurData` automatically.

After this file the blocker-specific construction has only two geometric
fields left:

* the chosen active 2x2 determinant has nonzero constant coefficient;
* the constant cleared binary Schur block has one of the supported rank-one
  pivot forms.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Canonical ring homomorphism moving the polynomial family parameter
outside the source polynomial ring. -/
noncomputable def polynomialFamilySeriesHom :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      Polynomial (MvPolynomial (Fin 4) K) :=
  MvPolynomial.eval₂Hom
    (Polynomial.mapRingHom
      (MvPolynomial.C :
        K →+* MvPolynomial (Fin 4) K))
    (fun i =>
      Polynomial.C (MvPolynomial.X i))

@[simp]
theorem polynomialFamilySeriesHom_C
    (c : Polynomial K) :
    polynomialFamilySeriesHom
        (K := K) (MvPolynomial.C c) =
      Polynomial.mapRingHom
        (MvPolynomial.C :
          K →+* MvPolynomial (Fin 4) K) c := by
  simp [polynomialFamilySeriesHom]

@[simp]
theorem polynomialFamilySeriesHom_C_X_pow
    (n : ℕ) :
    polynomialFamilySeriesHom
        (K := K)
        (MvPolynomial.C (Polynomial.X ^ n)) =
      Polynomial.X ^ n := by
  simp [polynomialFamilySeriesHom]

/-- The honest Hessian matrix of an adaptive endpoint, with the family
parameter moved to the outer polynomial ring. -/
noncomputable def adaptiveAlignedEndpointHessianSeriesMatrix
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    Matrix (Fin 4) (Fin 4)
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (polynomialFamilySeriesHom (K := K)).mapMatrix
    (HC4.Polynomial.hessian E.family)

/-- The polynomial-series Hessian remains symmetric. -/
theorem adaptiveAlignedEndpointHessianSeriesMatrix_symmetric
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    ∀ i j,
      adaptiveAlignedEndpointHessianSeriesMatrix E i j =
        adaptiveAlignedEndpointHessianSeriesMatrix E j i := by
  intro i j
  unfold adaptiveAlignedEndpointHessianSeriesMatrix
  change
    polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian E.family i j) =
      polynomialFamilySeriesHom (K := K)
        (HC4.Polynomial.hessian E.family j i)
  apply congrArg (polynomialFamilySeriesHom (K := K))
  change
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv i E.family) =
      MvPolynomial.pderiv i
        (MvPolynomial.pderiv j E.family)
  rw [pderiv_comm_commRing]

/-- Actual `2+2` four-block cut out of the honest adaptive-family Hessian. -/
noncomputable def adaptiveAlignedEndpointHessianFourBlock
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    (adaptiveAlignedEndpointHessianSeriesMatrix E)

/-- The matrix represented by the four-block is exactly the honest
polynomial-series Hessian. -/
theorem adaptiveAlignedEndpointHessianFourBlock_matrix
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointHessianFourBlock E).matrix =
      adaptiveAlignedEndpointHessianSeriesMatrix E := by
  exact
    GeneralFourBlock.matrix_ofSymmetricMatrix
      (adaptiveAlignedEndpointHessianSeriesMatrix E)
      (adaptiveAlignedEndpointHessianSeriesMatrix_symmetric E)

/-- Exact adaptive-family four-block determinant clock. -/
theorem adaptiveAlignedEndpointHessianFourBlock_determinantCore
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointHessianFourBlock E).determinantCore =
      Polynomial.X ^ E.defect := by
  rw [← GeneralFourBlock.matrix_det]
  rw [adaptiveAlignedEndpointHessianFourBlock_matrix]
  unfold adaptiveAlignedEndpointHessianSeriesMatrix
  rw [←
    (polynomialFamilySeriesHom (K := K)).map_det
      (HC4.Polynomial.hessian E.family)]
  change
    polynomialFamilySeriesHom
        (K := K) (HC4.Polynomial.hessianDeterminant E.family) =
      Polynomial.X ^ E.defect
  rw [E.hessianDefect]
  exact polynomialFamilySeriesHom_C_X_pow E.defect

/-- Once the two special-fibre chart facts are known, the honest endpoint
Hessian immediately packages as exact adaptive four-block Schur data. -/
noncomputable def AdaptiveAlignedSmithMinimalEndpoint.exactFourBlockSchurData_of_chart
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap)
    (hactive :
      (adaptiveAlignedEndpointHessianFourBlock E).activeDet.coeff 0 ≠ 0)
    (hrigid :
      (adaptiveAlignedEndpointHessianFourBlock E).polynomialSchurSeries.LeftPivot ∨
      (adaptiveAlignedEndpointHessianFourBlock E).polynomialSchurSeries.RightAxisPivot) :
    AdaptiveAlignedExactFourBlockSchurData E where
  block := adaptiveAlignedEndpointHessianFourBlock E
  fullDet :=
    adaptiveAlignedEndpointHessianFourBlock_determinantCore E
  activeDet_coeff_zero_ne_zero := hactive
  rigid := hrigid

/-- Blocker-facing version: the entire exact four-block/Schur certificate is
reduced to the two concrete chart facts on the honest endpoint Hessian. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.hasExactFourBlockSchurData_of_chart
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (hactive :
      (adaptiveAlignedEndpointHessianFourBlock B.aligned.endpoint).activeDet.coeff 0 ≠ 0)
    (hrigid :
      (adaptiveAlignedEndpointHessianFourBlock B.aligned.endpoint).polynomialSchurSeries.LeftPivot ∨
      (adaptiveAlignedEndpointHessianFourBlock B.aligned.endpoint).polynomialSchurSeries.RightAxisPivot) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B := by
  exact
    ⟨B.aligned.endpoint.exactFourBlockSchurData_of_chart
      hactive hrigid⟩

end

end HC4.Valuation
